import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pyy_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq21 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
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
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X1) (σ X0)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq56 X1 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | (have j1 := eq56 (τ X0) X1
       grind)
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq43 (σ X0)
       grind)
    | exact superpose eq43 eq22
    | exact resolve eq22 eq43
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
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq83
    | exact resolve eq83 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq84
    | exact resolve eq84 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
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
  have eq122 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq67
    | exact resolve eq67 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq152 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X2 (σ X0) X1 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq25
    | exact resolve eq25 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 X2 X3 : G, (M.op (τ X0) X1) = (M.op (M.op (M.op X2 X1) X3) (τ X0)) ∨ (σ (M.op (τ X0) X1)) = (k (σ (M.op (M.op X2 X1) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 X0 (M.op (M.op X3 X1) X0)
       have i₂ := eq25 X0 X1 (τ X0) X3
       grind)
    | exact superpose eq25 eq73
    | exact resolve eq73 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq371 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq152 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq95 (M.op X0 X0)
       grind)
    | exact superpose eq95 eq152
    | exact resolve eq152 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq387 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq125
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq125
    | (have j1 := eq56 (σ x) (σ y)
       grind)
    | exact resolve eq125 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq125
  have eq388 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq387
  have eq620 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (k (k X0 (σ X1)) (σ X2)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) (σ X2)
       have i₂ := eq122 X0 X1 X2
       grind)
    | exact superpose eq122 eq13
    | (have j0 := eq13 (k X0 (σ X1)) (σ X2)
       have j1 := eq122 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq122 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq122 X0 X1 X2
       grind)
    | exact resolve eq13 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X0 X1 X2 X3 : G, (M.op X3 (k X0 (σ X1))) = (M.op X3 (M.op (M.op (k X0 (σ X1)) (σ X2)) X3)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (k X0 (σ X1)) (σ X2)
       have i₂ := eq122 X0 X1 X2
       grind)
    | exact superpose eq122 eq9
    | (have j1 := eq122 X0 X1 X2
       grind)
    | exact resolve eq9 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq624 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (σ X2)) ∨ (k (k X0 (σ X1)) (σ X2)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq620 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq627 : ∀ X0 X1 X2 X3 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (M.op X3 (σ X2)) = (M.op X3 (k X0 (σ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq622 X0 X1 X2 X3
       have i₂ := eq9 X3 (σ X2) (k X0 (σ X1))
       grind)
    | exact superpose eq9 eq622
    | (have j0 := eq622 X0 X1 X2 X3
       grind)
    | exact resolve eq622 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq629 : ∀ X0 X1 X2 : G, (σ X2) = (σ (M.op X2 X2)) ∨ (k (k X0 (σ X1)) (σ X2)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq624 X0 X1 X2
       have i₂ := eq95 X2
       grind)
    | exact superpose eq95 eq624
    | (have j0 := eq624 X0 X1 X2
       grind)
    | exact resolve eq624 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq645 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) (σ X2)) = (σ (M.op X2 X2)) ∨ (σ X2) = (σ (M.op X2 X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq629 X0 X1 X2
       have i₂ := eq95 X2
       grind)
    | exact superpose eq95 eq629
    | (have j0 := eq629 X0 X1 X2
       grind)
    | exact resolve eq629 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq654 : ∀ X0 X1 X2 : G, (σ X2) = (σ (M.op X2 X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (σ (M.op X2 X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq645 X0 X1 X2
       have i₂ := eq21 X0 X1 X2
       grind)
    | exact superpose eq21 eq645
    | (have j0 := eq645 X0 X1 X2
       grind)
    | exact resolve eq645 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq645
  have eq1149 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) X1)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 x X0 y
       have i₂ := eq388
       grind)
    | exact superpose eq388 eq25
    | exact resolve eq25 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq1155 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1149 X0 x
       have i₂ := eq25 x y X0 x
       grind)
    | exact superpose eq25 eq1149
    | exact resolve eq1149 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1450 : ∀ X0 X1 X2 X3 : G, (M.op X3 (σ (M.op (M.op X0 X1) X2))) = (M.op X3 (σ (M.op (M.op (M.op (M.op X0 X1) X2) X1) (M.op (M.op (M.op X0 X1) X2) X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq371 (M.op (M.op X3 X1) X0) X1
       have i₂ := eq25 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | exact superpose eq25 eq371
    | exact resolve eq371 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq1531 : ∀ X0 X1 X2 X3 : G, (M.op X3 (σ (M.op (M.op X0 X1) X2))) = (M.op X3 (σ (M.op (M.op (M.op (M.op X0 X1) X2) X1) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1450 X0 X1 X2 X3
       have i₂ := eq25 X1 X2 (M.op (M.op (M.op X0 X1) X2) X1) (M.op X0 X1)
       grind)
    | exact superpose eq25 eq1450
    | exact resolve eq1450 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450
  have eq2815 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) ∨ (M.op X2 x) = (M.op X2 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 (σ x) X0 (σ y)
       have i₂ := eq1155 X2
       grind)
    | exact superpose eq1155 eq25
    | (have j1 := eq1155 X2
       grind)
    | exact resolve eq25 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq2821 : ∀ X0 X2 : G, (M.op X2 x) = (M.op X2 y) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0 X2
    first
    | (have i₁ := eq2815 X0 x X2
       have i₂ := eq25 x (σ y) X0 (σ x)
       grind)
    | exact superpose eq25 eq2815
    | (have j0 := eq2815 X0 x X2
       grind)
    | exact resolve eq2815 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2815
  have eq6362 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 X1) X2)) = (M.op (σ X2) (k (σ X0) (σ X1))) ∨ (M.op X3 (σ X2)) = (M.op X3 (k (σ X0) (σ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq627 (σ X0) X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq627
    | (have j0 := eq627 (σ X0) X1 X2 X3
       grind)
    | exact resolve eq627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq6503 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 X1) X2)) = (M.op (σ X2) (σ (k X0 X1))) ∨ (M.op X3 (σ X2)) = (M.op X3 (k (σ X0) (σ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6362 X0 X1 X2 X3
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6362
    | (have j0 := eq6362 X0 X1 X2 X3
       grind)
    | exact resolve eq6362 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6362
  have eq6529 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 X1) X2)) = (M.op (σ X2) (σ (k X0 X1))) ∨ (M.op X3 (σ X2)) = (M.op X3 (σ (k X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6503 X0 X1 X2 X3
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6503
    | (have j0 := eq6503 X0 X1 X2 X3
       grind)
    | exact resolve eq6503 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6503
  have eq7175 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (τ X0)) = (M.op X2 (M.op (M.op (τ X0) X1) X5)) ∨ (σ (M.op (τ X0) X1)) = (k (σ (M.op (M.op X3 X1) X4)) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq25 X5 (τ X0) X2 (M.op (M.op X3 X1) X4)
       have i₂ := eq330 X0 X1 X3 X4
       grind)
    | exact superpose eq330 eq25
    | (have j1 := eq330 X0 X1 X3 X4
       grind)
    | exact resolve eq25 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq7183 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op (τ X0) X1)) = (k (σ (M.op (M.op X3 X1) X4)) X0) ∨ (M.op X2 X1) = (M.op X2 (τ X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7175 X0 X1 X2 X3 X4 x
       have i₂ := eq25 x X1 X2 (τ X0)
       grind)
    | exact superpose eq25 eq7175
    | (have j0 := eq7175 X0 X1 X2 X3 X4 x
       grind)
    | exact resolve eq7175 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7175
  have eq14601 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (M.op X0 X0) = (σ (k (k (τ X1) X2) (τ X0))) ∨ (σ (k (k (τ X1) X2) (τ X0))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq654 X0 X1 (τ X0)
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq654
    | (have j0 := eq654 X1 X2 (τ X0)
       grind)
    | exact resolve eq654 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq14708 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (σ (k (k (τ X1) X2) (τ X0))) ∨ (σ (k (k (τ X1) X2) (τ X0))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14601 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14601
    | (have j0 := eq14601 X0 X1 X2
       grind)
    | exact resolve eq14601 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14601
  have eq14719 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (σ (k (τ X1) X2)) X0) ∨ (M.op X0 X0) = X0 ∨ (σ (k (k (τ X1) X2) (τ X0))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14708 X0 X1 X2
       have i₂ := eq18 X0 (k (τ X1) X2)
       grind)
    | exact superpose eq18 eq14708
    | (have j0 := eq14708 X0 X1 X2
       grind)
    | exact resolve eq14708 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14708
  have eq14730 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = X0 ∨ (σ (k (k (τ X1) X2) (τ X0))) = (M.op (σ (τ X0)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14719 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq14719
    | (have j0 := eq14719 X0 X1 X2
       grind)
    | exact resolve eq14719 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14719
  have eq14741 : ∀ X0 X1 X2 : G, (σ (k (k (τ X1) X2) (τ X0))) = (M.op X0 (k X1 (σ X2))) ∨ (M.op X0 X0) = (k (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14730 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14730
    | (have j0 := eq14730 X0 X1 X2
       grind)
    | exact resolve eq14730 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14730
  have eq14752 : ∀ X0 X1 X2 : G, (k (σ (k (τ X1) X2)) X0) = (M.op X0 (k X1 (σ X2))) ∨ (M.op X0 X0) = (k (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14741 X0 X1 X2
       have i₂ := eq18 X0 (k (τ X1) X2)
       grind)
    | exact superpose eq18 eq14741
    | (have j0 := eq14741 X0 X1 X2
       grind)
    | exact resolve eq14741 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14741
  have eq14761 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op X0 (k X1 (σ X2))) ∨ (M.op X0 X0) = (k (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14752 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq14752
    | (have j0 := eq14752 X0 X1 X2
       grind)
    | exact resolve eq14752 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq14752
  have eq14768 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op X0 (k X1 (σ X2))) ∨ (M.op X0 X0) = (k (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq14761 X0 X1 X2
       have j1 := eq12 (k X1 (σ X2)) X0
       grind)
    | (have r₁ := eq14761 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14761 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14761
  have eq34632 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op (τ (σ X0)) X1)) = (σ (k (M.op (M.op X2 X1) X3) X0)) ∨ (M.op X4 X1) = (M.op X4 (τ (σ X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq15 (M.op (M.op X2 X1) X3) X0
       have i₂ := eq7183 (σ X0) X1 X4 X2 X3
       grind)
    | exact superpose eq7183 eq15
    | (have j1 := eq7183 (σ X0) X1 X4 X3 X4
       grind)
    | exact resolve eq15 eq7183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7183
  have eq34775 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X0 X1)) = (σ (k (M.op (M.op X2 X1) X3) X0)) ∨ (M.op X4 X1) = (M.op X4 (τ (σ X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq34632 X0 X1 X2 X3 X4
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34632
    | (have j0 := eq34632 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq34632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34632
  have eq34853 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X0 X1)) = (σ (k (M.op (M.op X2 X1) X3) X0)) ∨ (M.op X4 X1) = (M.op X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq34775 X0 X1 X2 X3 X4
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34775
    | (have j0 := eq34775 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq34775 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34775
  have eq83755 : ∀ X0 X1 X2 : G, (k (k X1 X0) X2) = (M.op X2 (k X1 X0)) ∨ (M.op X2 X2) = (k (k X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14768 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14768
    | exact resolve eq14768 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14768
  have eq84510 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ (M.op X2 (k X0 X1)) ∨ (k (k X0 X1) X2) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq83755 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83755
  have eq84666 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 (M.op X0 X0)) ∨ (M.op X1 X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq84510 X0 X0 x
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq84510
    | exact resolve eq84510 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84510
  have eq84928 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op (M.op X2 X1) (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84666 (M.op X2 X1) X0
       have i₂ := eq25 (M.op X2 X1) X1 X0 X2
       grind)
    | exact superpose eq25 eq84666
    | (have j0 := eq84666 (M.op X2 X1) X0
       grind)
    | (have r₁ := eq84666 (M.op x X1) X1
       have r₂ := eq25 (M.op x X1) X1 X1 x
       grind)
    | (have r₁ := eq84666 X0 (M.op (M.op x (M.op X0 X0)) X0)
       have r₂ := eq25 X0 (M.op X0 X0) (M.op (M.op x (M.op X0 X0)) X0) x
       grind)
    | exact resolve eq84666 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84666
  have eq86777 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X1 X0) (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq84928 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84928
  have eq87140 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) X0
       have i₂ := eq86777 (σ X0) X1
       grind)
    | exact superpose eq86777 eq22
    | exact resolve eq22 eq86777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq87172 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0)))
       have i₂ := eq86777 (τ X0) X1
       grind)
    | exact superpose eq86777 eq18
    | exact resolve eq18 eq86777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86777
  have eq87300 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq87172 X0 X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq87172
    | exact resolve eq87172 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87172
  have eq87330 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq87140 X0 X1
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq87140
    | exact resolve eq87140 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87140
  have eq134556 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k (k X1 X2) X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (k X1 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6529 X1 X2 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6529
  have eq134557 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (σ (k (k X1 X2) X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (k X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134556 X0 X1 X2
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq134556
    | (have j0 := eq134556 X0 X1 X2
       grind)
    | exact resolve eq134556 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134556
  have eq134629 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (σ (k (k X1 X2) X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (k X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134557 X0 X1 X2
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq134557
    | (have j0 := eq134557 X0 X1 X2
       grind)
    | exact resolve eq134557 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134557
  have eq330464 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (σ (k (k X1 X2) (τ X0))) ∨ (M.op X0 X0) = (M.op (σ (τ X0)) (σ (k X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134629 (τ X0) X1 X2
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq134629
    | exact resolve eq134629 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq134629
  have eq330952 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (k (σ (k X1 X2)) X0) ∨ (M.op X0 X0) = (M.op (σ (τ X0)) (σ (k X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq330464 X0 X1 X2
       have i₂ := eq18 X0 (k X1 X2)
       grind)
    | exact superpose eq18 eq330464
    | (have j0 := eq330464 X0 X1 X2
       grind)
    | exact resolve eq330464 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq330464
  have eq331080 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (k (σ (k X1 X2)) X0) ∨ (M.op X0 X0) = (M.op X0 (σ (k X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq330952 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq330952
    | (have j0 := eq330952 X0 X1 X2
       grind)
    | exact resolve eq330952 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330952
  have eq332694 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k (σ (M.op X0 X0)) X1) ∨ (M.op X1 X1) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq331080 X0 X0 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq331080
    | (have r₁ := eq331080 (σ (k X1 x)) X1 x
       have r₂ := eq43 (σ (k X1 x))
       grind)
    | exact resolve eq331080 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq331080
  have eq359466 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 (σ (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq332694 (M.op X1 (τ X0)) X0
       have i₂ := eq87300 X0 X1
       grind)
    | exact superpose eq87300 eq332694
    | (have j0 := eq332694 (M.op X1 (τ X0)) X0
       grind)
    | (have r₁ := eq332694 (M.op X1 (τ X0)) X0
       have r₂ := eq87300 X0 X1
       grind)
    | exact resolve eq332694 eq87300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87300 eq332694
  have eq359510 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have j0 := eq359466 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359466
  have eq359688 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X2 (σ (M.op (M.op (M.op X0 X1) (τ X2)) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq359510 X2 (M.op X0 X1)
       have i₂ := eq25 (τ X2) X1 (M.op (M.op X0 X1) (τ X2)) X0
       grind)
    | exact superpose eq25 eq359510
    | exact resolve eq359510 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359510
  have eq361590 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (M.op X1 (τ X0)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq359688 (M.op X1 (τ X0)) X2 X0
       have i₂ := eq1531 X1 (τ X0) X2 X0
       grind)
    | exact superpose eq1531 eq359688
    | exact resolve eq359688 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531 eq359688
  have eq362677 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (σ (M.op (M.op X2 (τ X0)) X3))) = (M.op X1 (M.op (M.op X0 X0) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X4 (σ (M.op (M.op X2 (τ X0)) X3)) X1 X0
       have i₂ := eq361590 X0 X2 X3
       grind)
    | exact superpose eq361590 eq25
    | exact resolve eq25 eq361590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361590
  have eq363084 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (σ (M.op (M.op X2 (τ X0)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq362677 X0 X1 X2 X3 x
       have i₂ := eq25 x X0 X1 X0
       grind)
    | exact superpose eq25 eq362677
    | exact resolve eq362677 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq362677
  have eq365296 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X2 X0) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq363084 (σ X0) X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq363084
    | exact resolve eq363084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363084
  have eq367803 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ y)) = (M.op X1 (σ (M.op (M.op X0 x) X2))) ∨ (M.op X3 (σ x)) = (M.op X3 (σ y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq365296 y X1 X0 X2
       have i₂ := eq2821 X3 X0
       grind)
    | exact superpose eq2821 eq365296
    | (have j1 := eq2821 X3 X2
       grind)
    | exact resolve eq365296 eq2821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2821
  have eq368716 : ∀ X1 X3 : G, (M.op X1 (σ x)) = (M.op X1 (σ y)) ∨ (M.op X3 (σ x)) = (M.op X3 (σ y)) := by
    intro X1 X3
    first
    | (have i₁ := eq367803 x X1 x X3
       have i₂ := eq365296 x X1 x x
       grind)
    | exact superpose eq365296 eq367803
    | (have j0 := eq367803 x X1 x X1
       grind)
    | exact resolve eq367803 eq365296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365296 eq367803
  have eq428987 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq368716 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368716
  have eq428988 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq428987 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428987
  have eq430277 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq428988 (σ y)
       have i₂ := eq95 y
       grind)
    | exact superpose eq95 eq428988
    | exact resolve eq428988 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430702 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq428988 (σ x)
       grind)
    | exact superpose eq428988 eq16
    | exact resolve eq16 eq428988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428988
  have eq430937 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq430702
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq430702
    | exact resolve eq430702 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq430702
  have eq433657 : (M.op x x) = (k (τ (M.op (σ (M.op y y)) (σ (M.op y y)))) x) := by
    first
    | (have i₁ := eq87330 x (σ y)
       have i₂ := eq430277
       grind)
    | exact superpose eq430277 eq87330
    | exact resolve eq87330 eq430277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87330 eq430277
  have eq433747 : (M.op x x) = (k (M.op (M.op y y) (M.op y y)) x) := by
    first
    | (have i₁ := eq433657
       have i₂ := eq92 (M.op y y)
       grind)
    | exact superpose eq92 eq433657
    | exact resolve eq433657 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq433657
  have eq449938 : ∀ X0 : G, (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq34853 x y y (M.op y y) X0
       have i₂ := eq433747
       grind)
    | exact superpose eq433747 eq34853
    | (have j0 := eq34853 y x x x X0
       grind)
    | exact resolve eq34853 eq433747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34853 eq433747
  have eq450117 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq449938 X0
       grind)
    | (have r₁ := eq449938 X0
       have r₂ := eq430937
       grind)
    | exact resolve eq449938 eq430937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449938
  have eq450722 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq430937
       have i₂ := eq450117 x
       grind)
    | exact superpose eq450117 eq430937
    | exact resolve eq430937 eq450117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430937 eq450117
  have eq450728 : False := by grind
  exact eq450728

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxx_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  clear eq24
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq73 y x
       grind)
    | exact superpose eq73 eq70
    | (have j1 := eq73 y x
       grind)
    | exact resolve eq70 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq104
    | exact resolve eq104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106 eq73
    | (have j0 := eq73 (σ y) (σ x)
       grind)
    | exact resolve eq73 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq120
    | exact resolve eq120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq121
       have r₂ := eq27
       grind)
    | exact resolve eq121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq126 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq223 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq126 eq51
    | exact resolve eq51 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq232 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq223
    | (have j0 := eq223 (σ y)
       grind)
    | exact resolve eq223 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq246 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq126 eq232
    | exact resolve eq232 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq249 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq246
  have eq275 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ x)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq249 eq14
    | exact resolve eq14 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq277 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq14 X0 sF2 sF3
       grind)
    | exact superpose eq14 eq275
    | exact resolve eq275 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq290 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq277
    | (have j0 := eq277 (σ x)
       grind)
    | exact resolve eq277 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq329 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq290 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | exact resolve eq13 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq334 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq329 X0
       grind)
    | (have r₁ := eq329 X0
       have r₂ := eq126
       grind)
    | exact resolve eq329 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq329
  have eq377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq334 eq106
    | exact resolve eq106 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq334
  have eq380 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq377
  have eq383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq380
    | exact resolve eq380 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq385 : x = (M.op x y) := by
    first
    | (have r₁ := eq383
       have r₂ := eq27
       grind)
    | exact resolve eq383 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq387 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq385 eq20
    | exact resolve eq20 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq385 eq50
    | exact resolve eq50 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq399 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq387
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq387
    | exact resolve eq387 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq387
  have eq401 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq399 eq26
    | exact resolve eq26 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq442 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq389 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq389
    | (have j0 := eq389 y
       grind)
    | exact resolve eq389 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq464 : (M.op y x) = (M.op y y) := by
    first
    | exact superpose eq385 eq442
    | exact resolve eq442 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq548 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq464
       grind)
    | exact superpose eq464 eq14
    | exact resolve eq14 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq549 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq548 X0
       have i₂ := eq14 X0 x y
       grind)
    | exact superpose eq14 eq548
    | exact resolve eq548 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq558 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq549 x
       grind)
    | exact superpose eq549 eq18
    | (have j1 := eq549 x
       grind)
    | exact resolve eq18 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq565 : x = (M.op x x) := by
    first
    | exact superpose eq385 eq558
    | exact resolve eq558 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq558
  have eq572 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq565
       grind)
    | exact superpose eq565 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq565
       grind)
    | exact resolve eq13 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq575 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq572 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq582 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq575 y
       grind)
    | exact superpose eq575 eq70
    | exact resolve eq70 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq575
  have eq587 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq399 eq582
    | exact resolve eq582 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq582
  have eq591 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq587
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq587
    | exact resolve eq587 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq587
  have eq594 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq591
    | exact resolve eq591 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq591
  have eq601 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq594 eq73
    | (have j0 := eq73 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq73 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq594
  have eq602 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq601
  have eq604 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq401 eq602
    | exact resolve eq602 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq602
  have eq607 : False := by grind
  exact eq607

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxy_pxx_pyx_Equation3600 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq110 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq110
    | exact resolve eq110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq111 (σ X0) (σ X0) x
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq111
    | exact resolve eq111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 (M.op X0 X1) X1
       have i₂ := eq111 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq111 eq112
    | exact resolve eq112 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq657 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq659 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq662 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq657 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq657
    | (have j0 := eq657 X0 X1
       grind)
    | exact resolve eq657 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq3837 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq662 x y
       grind)
    | exact superpose eq662 eq16
    | (have j1 := eq662 x y
       grind)
    | exact resolve eq16 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq9789 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq659 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq659
    | exact resolve eq659 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq9914 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9789 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9789
    | (have j0 := eq9789 X0 X1
       grind)
    | exact resolve eq9789 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9789
  have eq10742 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3837
       have i₂ := eq9914 y x
       grind)
    | exact superpose eq9914 eq3837
    | (have j1 := eq9914 y x
       grind)
    | (have r₁ := eq3837
       have r₂ := eq9914 y x
       grind)
    | (have r₁ := eq3837
       have r₂ := eq9914 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3837
       have r₂ := eq9914 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3837 eq9914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3837 eq9914
  have eq10743 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq10742
  have eq39429 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10743
       grind)
    | exact superpose eq10743 eq16
    | exact resolve eq16 eq10743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10743
  have eq39430 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq39429
       have r₂ := eq23 x
       grind)
    | exact resolve eq39429 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39429
  have eq39433 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq39430
       grind)
    | exact superpose eq39430 eq10
    | exact resolve eq10 eq39430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39430
  have eq39493 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq39433
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq39433
    | exact resolve eq39433 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39433
  have eq39496 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39493
       grind)
    | exact superpose eq39493 eq16
    | exact resolve eq16 eq39493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39493
  have eq39497 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq39496
       have r₂ := eq23 x
       grind)
    | exact resolve eq39496 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq39496
  have eq39543 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq39497
       grind)
    | exact superpose eq39497 eq10
    | exact resolve eq10 eq39497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39497
  have eq39619 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39543
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq39543
    | exact resolve eq39543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39543
  have eq39620 : y = (M.op x x) := by grind
  clear eq39619
  have eq39777 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq111 x x x
       have i₂ := eq39620
       grind)
    | exact superpose eq39620 eq111
    | exact resolve eq111 eq39620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq39779 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq136 x x x
       have i₂ := eq39620
       grind)
    | exact superpose eq39620 eq136
    | exact resolve eq136 eq39620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq39620
  have eq40270 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39779 (σ x)
       grind)
    | exact superpose eq39779 eq16
    | exact resolve eq16 eq39779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39779
  have eq40291 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq40270
       have i₂ := eq39777 x
       grind)
    | exact superpose eq39777 eq40270
    | exact resolve eq40270 eq39777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39777 eq40270
  have eq40292 : False := by grind
  exact eq40292

/-- `Equation3690`: `x ◇ x = (y ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation3690 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3690 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3690.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq424 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq429 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq424 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq424 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq424 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq424 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq424 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq3333 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq429
  have eq3409 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3333 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3333
  have eq707853 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3409 (σ X1) (σ X0)
       grind)
    | exact superpose eq3409 eq15
    | exact resolve eq15 eq3409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707878 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq707853 X0 X1
       have i₂ := eq3409 X1 X0
       grind)
    | exact superpose eq3409 eq707853
    | exact resolve eq707853 eq3409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409 eq707853
  have eq707924 : False := by grind
  exact eq707924

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pxx_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 X3) (M.op X2 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq80 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq81 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq80
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq113 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) ≠ (M.op (M.op X0 X1) (M.op X0 X2)) ∨ (M.op (M.op X0 X1) (M.op X0 X2)) = X2 ∨ (M.op (M.op X0 X1) (M.op X0 X2)) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have r₁ := eq12 (M.op X1 (M.op X1 X2)) (M.op X1 X2)
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (k X2 X2) ∨ (M.op (M.op X0 X1) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq113 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq162 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq140 eq16
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq213 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op x y) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq55 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 y
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq35
  have eq372 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq468 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op X1 X2) (M.op X1 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X3 X1 X2
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq52
    | exact resolve eq52 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq56
  have eq550 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq283 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq283
    | exact resolve eq283 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq1953 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x y) (M.op x X0))) = (k (M.op (M.op x y) (M.op x X0)) (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq73 X0 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq73
    | exact resolve eq73 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1997 : ∀ X0 : G, (M.op (M.op x X0) (M.op x X0)) = (k (M.op (M.op x y) (M.op x X0)) (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq1953 X0
       have i₂ := eq14 (M.op x X0) sF0 (M.op x X0)
       grind)
    | exact superpose eq14 eq1953
    | exact resolve eq1953 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq2019 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op x y) (M.op x X0)) (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq1997 X0
       have i₂ := eq14 X0 x X0
       grind)
    | exact superpose eq14 eq1997
    | exact resolve eq1997 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997
  have eq2798 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (M.op X1 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 X2
       have i₂ := eq120 X1 X2 X0
       grind)
    | exact superpose eq120 eq14
    | (have j1 := eq120 X1 X2 X0
       grind)
    | exact resolve eq14 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq3607 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq8971 : ∀ X0 X3 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op x y) (M.op x (M.op X3 X0))) := by
    intro X0 X3
    first
    | (have i₁ := eq468 X0 x x X3
       have i₂ := eq213 x x (M.op X3 X0)
       grind)
    | (have i₁ := eq468 X0 x y X3
       have i₂ := eq213 X0 x (M.op X3 X0)
       grind)
    | exact superpose eq213 eq468
    | (have j0 := eq468 X0 x y X3
       grind)
    | exact resolve eq468 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq8972 : ∀ X0 X3 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x (M.op X3 X0))) := by
    intro X0 X3
    first
    | exact superpose eq235 eq8971
    | exact resolve eq8971 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq8971
  have eq17610 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2798 X0 x x
       have i₂ := eq213 x x X0
       grind)
    | (have i₁ := eq2798 x x y
       have i₂ := eq213 X0 x x
       grind)
    | exact superpose eq213 eq2798
    | (have j0 := eq2798 X0 x y
       grind)
    | exact resolve eq2798 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq2798
  have eq17867 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq17610 eq2019
    | (have j1 := eq17610 X0
       grind)
    | exact resolve eq2019 eq17610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019 eq17610
  have eq17921 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq17867 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17867
  have eq17992 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq17921 (σ X0)
       grind)
    | exact superpose eq17921 eq10
    | exact resolve eq10 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17996 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq550 X0 X0
       have i₂ := eq17921 (τ X0)
       grind)
    | exact superpose eq17921 eq550
    | exact resolve eq550 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq18004 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq17921 x
       grind)
    | exact superpose eq17921 eq44
    | exact resolve eq44 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq18013 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq81
       have i₂ := eq17921 y
       grind)
    | exact superpose eq17921 eq81
    | exact resolve eq81 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq18034 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq162
       have i₂ := eq17921 sF1
       grind)
    | exact superpose eq17921 eq162
    | exact resolve eq162 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq18043 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq17921 sF2
       grind)
    | exact superpose eq17921 eq50
    | exact resolve eq50 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq18075 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq18043
       have i₂ := eq17921 x
       grind)
    | exact superpose eq17921 eq18043
    | exact resolve eq18043 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18043
  have eq18084 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq18034
       have i₂ := eq17921 sF0
       grind)
    | exact superpose eq17921 eq18034
    | exact resolve eq18034 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18034
  have eq18104 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq18013
       have i₂ := eq17921 sF3
       grind)
    | exact superpose eq17921 eq18013
    | exact resolve eq18013 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18013
  have eq18113 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18004
       have i₂ := eq17921 sF2
       grind)
    | exact superpose eq17921 eq18004
    | exact resolve eq18004 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18004
  have eq18121 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17996 X0
       have i₂ := eq17921 X0
       grind)
    | exact superpose eq17921 eq17996
    | exact resolve eq17996 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17996
  have eq18125 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17992 X0
       have i₂ := eq17921 X0
       grind)
    | exact superpose eq17921 eq17992
    | exact resolve eq17992 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17921 eq17992
  have eq18147 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq215 eq18084
    | exact resolve eq18084 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18084
  have eq18482 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y y)) := by
    first
    | exact superpose eq18147 eq15
    | exact resolve eq15 eq18147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18147
  have eq18534 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq18482
       have i₂ := eq18104
       grind)
    | exact superpose eq18104 eq18482
    | exact resolve eq18482 eq18104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18482
  have eq18720 : ∀ X0 : G, (M.op (M.op x y) (M.op x (τ X0))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18121 X0
       have i₂ := eq55 (τ X0)
       grind)
    | exact superpose eq55 eq18121
    | exact resolve eq18121 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19756 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (M.op x y) (M.op x (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op X0 X0)
       have i₂ := eq18720 X0
       grind)
    | exact superpose eq18720 eq15
    | exact resolve eq15 eq18720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18720
  have eq21764 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op (M.op x y) (M.op x (τ (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq18125 X0
       have i₂ := eq19756 (σ X0)
       grind)
    | exact superpose eq19756 eq18125
    | exact resolve eq18125 eq19756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19756
  have eq21818 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq21764 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq21764
    | exact resolve eq21764 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21764
  have eq27869 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq18121 X0
       grind)
    | exact superpose eq18121 eq372
    | exact resolve eq372 eq18121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq18121
  have eq27870 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq27869 X0
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq27869
    | exact resolve eq27869 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27869
  have eq27871 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    grind
  clear eq27870
  have eq27882 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq27871 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq27871
    | exact resolve eq27871 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27871
  have eq28191 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq27882 X0
       have i₂ := eq18125 X0
       grind)
    | exact superpose eq18125 eq27882
    | exact resolve eq27882 eq18125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27882
  have eq28318 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq28191 X0
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq28191
    | exact resolve eq28191 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28191
  have eq87856 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3607 X0 X1
       have i₂ := eq18125 X0
       grind)
    | exact superpose eq18125 eq3607
    | (have j0 := eq3607 X0 X1
       grind)
    | exact resolve eq3607 eq18125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3607
  have eq87857 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87856 X0 X1
       have i₂ := eq18125 X0
       grind)
    | exact superpose eq18125 eq87856
    | (have j0 := eq87856 X0 X1
       grind)
    | exact resolve eq87856 eq18125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18125 eq87856
  have eq104119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq104119
    | exact resolve eq104119 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104119
  have eq104131 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq104120
       have r₂ := eq28
       grind)
    | exact resolve eq104120 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104120
  have eq104135 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq104131
    | exact resolve eq104131 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104131
  have eq104139 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq104135 eq116
    | (have r₁ := eq116
       have r₂ := eq104135
       grind)
    | exact resolve eq116 eq104135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq104270 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq104135 eq14
    | exact resolve eq14 eq104135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104328 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq104135
  have eq104330 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq104139
  have eq104370 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq60 eq104270
    | exact resolve eq104270 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq104270
  have eq104386 : (k (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18534 eq104330
    | exact resolve eq104330 eq18534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104330
  have eq104416 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18534 eq104370
    | exact resolve eq104370 eq18534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104370
  have eq163639 : (k (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq104386
       have r₂ := eq104328
       grind)
    | exact resolve eq104386 eq104328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104328 eq104386
  have eq163714 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq163639 eq101
    | exact resolve eq101 eq163639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq163639
  have eq163724 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq163714
  have eq163829 : (τ (σ y)) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq163724 eq18075
    | exact resolve eq18075 eq163724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163724
  have eq164103 : y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30 eq163829
    | exact resolve eq163829 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163829
  have eq164104 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq164103
  have eq164177 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq164104 eq104416
    | exact resolve eq104416 eq164104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104416 eq164104
  have eq164430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq164177
  have eq164496 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq164430
       have r₂ := eq28
       grind)
    | exact resolve eq164430 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164430
  have eq164525 : (τ (σ y)) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq164496 eq18075
    | exact resolve eq18075 eq164496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164496
  have eq164799 : y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq164525
    | exact resolve eq164525 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164525
  have eq164800 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq164799
  have eq164842 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op y y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq164800
       grind)
    | exact superpose eq164800 eq115
    | (have r₁ := eq115
       have r₂ := eq164800
       grind)
    | exact resolve eq115 eq164800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq164851 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18113
       have i₂ := eq164800
       grind)
    | exact superpose eq164800 eq18113
    | exact resolve eq18113 eq164800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164986 : (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21818 x
       have i₂ := eq164800
       grind)
    | exact superpose eq164800 eq21818
    | exact resolve eq21818 eq164800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21818
  have eq165098 : y ≠ (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq164800
  have eq165100 : y = (M.op x y) ∨ (M.op y y) = (k y x) ∨ y = (M.op x x) := by grind
  clear eq164842
  have eq165158 : (σ (M.op x y)) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq215 eq164986
    | exact resolve eq164986 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq164986
  have eq165219 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq164851
    | exact resolve eq164851 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164851
  have eq165254 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq165158
       have i₂ := eq18104
       grind)
    | exact superpose eq18104 eq165158
    | exact resolve eq165158 eq18104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165158
  have eq165289 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18534 eq165254
    | exact resolve eq165254 eq18534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165254
  have eq165304 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq165289
    | exact resolve eq165289 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165289
  have eq167646 : (M.op (M.op x y) (M.op x (σ x))) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq165219 eq8972
    | exact resolve eq8972 eq165219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8972 eq165219
  have eq167705 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (M.op x (σ x))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq55 eq167646
    | exact resolve eq167646 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167646
  have eq167775 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq55 eq167705
    | exact resolve eq167705 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq167705
  have eq250972 : (M.op y y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq165100
       have r₂ := eq165098
       grind)
    | exact resolve eq165100 eq165098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165098 eq165100
  have eq250983 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87857 x y
       have i₂ := eq250972
       grind)
    | exact superpose eq250972 eq87857
    | (have j0 := eq87857 x y
       grind)
    | exact resolve eq87857 eq250972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87857 eq250972
  have eq250988 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq250983
       have i₂ := eq18104
       grind)
    | exact superpose eq18104 eq250983
    | exact resolve eq250983 eq18104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250983
  have eq250999 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq250988
       have i₂ := eq18113
       grind)
    | exact superpose eq18113 eq250988
    | exact resolve eq250988 eq18113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250988
  have eq251003 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18534 eq250999
    | exact resolve eq250999 eq18534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250999
  have eq251004 : (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq251003
       have r₂ := eq167775
       grind)
    | exact resolve eq251003 eq167775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167775 eq251003
  have eq251005 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq251004
       have i₂ := eq18113
       grind)
    | exact superpose eq18113 eq251004
    | exact resolve eq251004 eq18113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18113 eq251004
  have eq251006 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq251005
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq251005
    | exact resolve eq251005 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251005
  have eq251007 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq251006
       have i₂ := eq18104
       grind)
    | exact superpose eq18104 eq251006
    | exact resolve eq251006 eq18104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18104 eq251006
  have eq251008 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18534 eq251007
    | exact resolve eq251007 eq18534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18534 eq251007
  have eq251009 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq251008
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq251008
    | exact resolve eq251008 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251008
  have eq251010 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq251009
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq251009
    | exact resolve eq251009 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251009
  have eq251011 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq251010
    | exact resolve eq251010 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251010
  have eq279553 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq251011 eq165304
    | exact resolve eq165304 eq251011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165304 eq251011
  have eq279924 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq279553
  have eq279988 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq279924
       have r₂ := eq28
       grind)
    | exact resolve eq279924 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279924
  have eq280047 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq279988 eq18075
    | exact resolve eq18075 eq279988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18075 eq279988
  have eq280481 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq280047
    | exact resolve eq280047 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq280047
  have eq280482 : y = (M.op x x) := by grind
  clear eq280481
  have eq280709 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28318 x
       have i₂ := eq280482
       grind)
    | exact superpose eq280482 eq28318
    | exact resolve eq28318 eq280482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28318 eq280482
  have eq280839 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq280709
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq280709
    | exact resolve eq280709 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq280709
  have eq280910 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq280839
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq280839
    | exact resolve eq280839 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq280839
  have eq280937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq280910
    | exact resolve eq280910 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq280910
  have eq280944 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq280937
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq280937
    | exact resolve eq280937 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq280937
  have eq280946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq280944
    | exact resolve eq280944 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq280944
  have eq280948 : False := by grind
  exact eq280948

/-- `Equation3737`: `x ◇ y = (x ◇ z) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxy_x_pxy_Equation3737 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3737 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3737.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X2)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op (M.op X1 X2) (M.op X0 X2)) = (k (M.op X1 X2) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X2) (M.op X0 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 X2) (M.op X0 X2)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq9 X0 X0 X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X1 X0) = (k (M.op X1 X2) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq34
    | (have j0 := eq34 X0 X1 X2
       grind)
    | (have r₁ := eq34 X0 (M.op X0 X2) (M.op (M.op X0 X2) X2)
       have r₂ := eq9 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq34 (M.op (M.op X1 X2) X2) (M.op X1 X2) X1
       have r₂ := eq9 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq71 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X2 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 (M.op X0 X2)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X2 X1)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq71 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq71 X1 X1 X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq71 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq71 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq556 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq572 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq556 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq556 X0
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq556
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq556 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq572 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq572 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq572 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq861 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq862 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq861 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq933 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X0
       have i₂ := eq583 X0 X1
       grind)
    | exact superpose eq583 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq583 X0 X1
       grind)
    | exact resolve eq14 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq942 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ X0)
       have i₂ := eq583 (σ X0) X1
       grind)
    | exact superpose eq583 eq31
    | (have j1 := eq583 (σ X0) X1
       grind)
    | exact resolve eq31 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq957 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq583 X1 (τ X0)
       grind)
    | exact superpose eq583 eq18
    | (have j1 := eq583 X1 X1
       grind)
    | exact resolve eq18 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq583
  have eq962 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq933 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq973 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq942 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq942
    | (have j0 := eq942 X0 X1
       grind)
    | exact resolve eq942 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq996 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq862 (M.op X0 X0)
       have i₂ := eq556 X0
       grind)
    | exact superpose eq556 eq862
    | (have j0 := eq862 (M.op X0 X0)
       grind)
    | exact resolve eq862 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq862
  have eq1005 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq996 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1105 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X0 X0 X0
       have i₂ := eq962 X0 X1
       grind)
    | exact superpose eq962 eq77
    | (have j0 := eq77 X1 X0 X2
       have j1 := eq962 X1 X0
       grind)
    | exact resolve eq77 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq1149 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1105 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1105 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1105 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1386 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) X1) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq1005 X0
       grind)
    | exact superpose eq1005 eq77
    | (have j0 := eq77 X1 (σ (M.op X0 X0)) x
       grind)
    | exact resolve eq77 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1005
  have eq1396 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1386 X0 X1
       have j1 := eq12 (σ (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq1386 X0 X1
       have r₂ := eq12 (σ (M.op X0 X0)) X1
       grind)
    | exact resolve eq1386 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq2280 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X0) X1
       have i₂ := eq1396 X0 (σ X1)
       grind)
    | exact superpose eq1396 eq15
    | exact resolve eq15 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3964 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq973 X1 (σ X0)
       grind)
    | exact superpose eq973 eq15
    | (have j1 := eq973 X1 X1
       grind)
    | exact resolve eq15 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq4462 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1149 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq4463 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4462 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4462
  have eq5145 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4463 (σ X0)
       grind)
    | exact superpose eq4463 eq15
    | exact resolve eq15 eq4463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5149 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq4463 (τ X0)
       grind)
    | exact superpose eq4463 eq36
    | exact resolve eq36 eq4463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq5154 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5149 X0
       have i₂ := eq4463 X0
       grind)
    | exact superpose eq4463 eq5149
    | exact resolve eq5149 eq4463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5149
  have eq5158 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5145 X0
       have i₂ := eq4463 X0
       grind)
    | exact superpose eq4463 eq5145
    | exact resolve eq5145 eq4463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5145
  have eq5732 : ∀ X0 X1 : G, (M.op (σ (τ (M.op X0 X0))) X1) = (k (σ (τ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1396 (τ X0) X1
       have i₂ := eq5154 X0
       grind)
    | exact superpose eq5154 eq1396
    | exact resolve eq1396 eq5154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396 eq5154
  have eq5778 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5732 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq5732
    | exact resolve eq5732 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5732
  have eq6432 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq5158 X0
       grind)
    | exact superpose eq5158 eq9
    | exact resolve eq9 eq5158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5158
  have eq19846 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (M.op (σ (M.op X1 X1)) (σ (k (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6432 X1 (σ (M.op X0 X0))
       have i₂ := eq2280 X0 X1
       grind)
    | exact superpose eq2280 eq6432
    | exact resolve eq6432 eq2280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6432
  have eq19989 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (k (M.op X1 X1) (k (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19846 X0 X1
       have i₂ := eq2280 X1 (k (M.op X0 X0) X1)
       grind)
    | exact superpose eq2280 eq19846
    | exact resolve eq19846 eq2280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2280 eq19846
  have eq20075 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (M.op (M.op X1 X1) (k (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19989 X0 X1
       have i₂ := eq5778 X1 (k (M.op X0 X0) X1)
       grind)
    | exact superpose eq5778 eq19989
    | exact resolve eq19989 eq5778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19989
  have eq20112 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (M.op (M.op X1 X1) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq20075 X0 X1
       have i₂ := eq5778 X0 X1
       grind)
    | exact superpose eq5778 eq20075
    | exact resolve eq20075 eq5778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5778 eq20075
  have eq20120 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20112 X0 X1
       have i₂ := eq9 X1 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq20112
    | exact resolve eq20112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20112
  have eq77267 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq957 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq957
    | (have j0 := eq957 X0 X1
       grind)
    | exact resolve eq957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq77731 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77267 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq77267
    | (have j0 := eq77267 X0 X1
       grind)
    | exact resolve eq77267 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77267
  have eq77846 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77731 X0 X1
       have i₂ := eq4463 X1
       grind)
    | exact superpose eq4463 eq77731
    | (have j0 := eq77731 X0 X1
       grind)
    | exact resolve eq77731 eq4463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77731
  have eq112615 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3964 x y
       grind)
    | exact superpose eq3964 eq16
    | (have j1 := eq3964 x y
       grind)
    | exact resolve eq16 eq3964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3964
  have eq113204 : y = (M.op y y) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq112615
       have i₂ := eq4463 y
       grind)
    | exact superpose eq4463 eq112615
    | exact resolve eq112615 eq4463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4463 eq112615
  have eq113385 : y = (M.op y y) := by
    first
    | (have j1 := eq77846 x y
       grind)
    | (have r₁ := eq113204
       have r₂ := eq77846 x y
       grind)
    | exact resolve eq113204 eq77846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77846 eq113204
  have eq114239 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq20120 y x
       have i₂ := eq113385
       grind)
    | exact superpose eq113385 eq20120
    | exact resolve eq20120 eq113385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20120 eq113385
  have eq149657 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114239 x
       grind)
    | exact superpose eq114239 eq16
    | (have r₁ := eq16
       have r₂ := eq114239 x
       grind)
    | exact resolve eq16 eq114239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114239
  have eq149893 : False := by grind
  exact eq149893

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_pyy_pyx_pyy_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq263 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq263 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq263 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq263 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq275 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq264 (σ X0)
       grind)
    | exact superpose eq264 eq15
    | exact resolve eq15 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq275
    | exact resolve eq275 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq275
  have eq391 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq391 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq401 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq400 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq425 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq401 (σ X0) (σ X1)
       grind)
    | exact superpose eq401 eq15
    | (have j1 := eq401 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq401 X0 (τ X1)
       grind)
    | exact superpose eq401 eq17
    | (have j1 := eq401 X0 (τ X1)
       grind)
    | exact resolve eq17 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq401
  have eq442 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 X1
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq425
    | (have j0 := eq425 X0 X1
       grind)
    | exact resolve eq425 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq453 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq433 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq433
    | exact resolve eq433 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq491 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq453 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq453
    | (have j0 := eq453 X0 X1
       grind)
    | exact resolve eq453 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq810 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq442 x y
       grind)
    | exact superpose eq442 eq16
    | (have j1 := eq442 x y
       grind)
    | exact resolve eq16 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq442 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq842 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq810
       have i₂ := eq491 y x
       grind)
    | exact superpose eq491 eq810
    | (have j1 := eq491 y x
       grind)
    | (have r₁ := eq810
       have r₂ := eq491 y x
       grind)
    | exact resolve eq810 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq843 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq842
  have eq847 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq843
       grind)
    | exact superpose eq843 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq843
       grind)
    | exact resolve eq13 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : x = (M.op y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq847
  have eq7323 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq850
       grind)
    | exact superpose eq850 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq850
       grind)
    | exact resolve eq12 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq7325 : (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7323
  have eq28339 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq826 x y
       have i₂ := eq7325
       grind)
    | exact superpose eq7325 eq826
    | (have j0 := eq826 x y
       grind)
    | exact resolve eq826 eq7325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7325
  have eq28384 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq28339
  have eq28385 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq28384
  have eq28398 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28385
       grind)
    | exact superpose eq28385 eq16
    | exact resolve eq16 eq28385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28385
  have eq28561 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq28398
       have i₂ := eq843
       grind)
    | exact superpose eq843 eq28398
    | exact resolve eq28398 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843 eq28398
  have eq28575 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq28561
  have eq28589 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq826 x y
       have i₂ := eq28575
       grind)
    | exact superpose eq28575 eq826
    | (have j0 := eq826 x y
       grind)
    | exact resolve eq826 eq28575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826 eq28575
  have eq28633 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq28589
  have eq28634 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq28633
  have eq28647 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28634
       grind)
    | exact superpose eq28634 eq16
    | exact resolve eq16 eq28634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28657 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq28634
       grind)
    | exact superpose eq28634 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq28634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28678 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq28657
       have r₂ := eq294 x
       grind)
    | exact resolve eq28657 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28657
  have eq28681 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq28678
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq28678
    | exact resolve eq28678 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28678
  have eq28682 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq28681
       have i₂ := eq294 x
       grind)
    | exact superpose eq294 eq28681
    | exact resolve eq28681 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq28681
  have eq35900 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq28682
       grind)
    | exact superpose eq28682 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq28682
       grind)
    | exact resolve eq12 eq28682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28682
  have eq35911 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq35900
  have eq35922 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq35911
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq35911
    | exact resolve eq35911 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35911
  have eq35949 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq35922
       have i₂ := eq28634
       grind)
    | exact superpose eq28634 eq35922
    | exact resolve eq35922 eq28634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28634 eq35922
  have eq35950 : (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq35949
  have eq35978 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq491 y x
       have i₂ := eq35950
       grind)
    | exact superpose eq35950 eq491
    | (have j0 := eq491 y x
       grind)
    | exact resolve eq491 eq35950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq35950
  have eq36127 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq35978
       have r₂ := eq28647
       grind)
    | exact resolve eq35978 eq28647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35978
  have eq36284 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq28647
       have i₂ := eq36127
       grind)
    | exact superpose eq36127 eq28647
    | exact resolve eq28647 eq36127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28647 eq36127
  have eq36297 : False := by grind
  exact eq36297

/-- `Equation3888`: `x ◇ x = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_pyx_pxy_Equation3888 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3888 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3888.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  clear eq36
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
  have eq86 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
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
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
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
  have eq117 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq48
    | (have j0 := eq48 (M.op x y)
       grind)
    | exact resolve eq48 eq20
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
  have eq164 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq86 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq86
    | exact resolve eq86 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq176 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X1 (M.op (M.op X0 (M.op X0 X1)) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X1 (M.op X1 X0))
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (M.op y y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq16 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X0) ≠ X1 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq390 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq306
    | exact resolve eq306 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq534 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (k X1 X1) ∨ (M.op (M.op X0 (M.op X0 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X0
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq28
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X0
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (k X0 X1)) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : (M.op x y) = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq540 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq540 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq540 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq554 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq547
       grind)
    | exact superpose eq547 eq41
    | exact resolve eq41 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq554
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq554
    | exact resolve eq554 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq557 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq555
    | exact resolve eq555 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq567 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq557 eq549
    | exact resolve eq549 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq567
       have r₂ := eq27
       grind)
    | exact resolve eq567 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq579 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq574 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : (M.op (σ x) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq574 eq16
    | exact resolve eq16 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq574 eq580
    | exact resolve eq580 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq582 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq579
    | exact resolve eq579 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq584 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq581
    | exact resolve eq581 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq587 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq584 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq584 eq16
    | exact resolve eq16 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq179 eq588
    | exact resolve eq588 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq600 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq582 eq108
    | exact resolve eq108 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq582
  have eq603 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq600
    | exact resolve eq600 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq644 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq574 eq12
    | (have j0 := eq12 x (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq574
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq574
       grind)
    | exact resolve eq12 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq646
  have eq649 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq557 eq648
    | exact resolve eq648 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq658 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq649 eq589
    | exact resolve eq589 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq649 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq649
       grind)
    | exact resolve eq13 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq659 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq662 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq658
  have eq668 : x = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq662
       grind)
    | exact superpose eq662 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : (M.op x x) = (M.op (M.op y x) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq662
       grind)
    | exact superpose eq662 eq16
    | exact resolve eq16 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq662 eq669
    | exact resolve eq669 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq672 : x = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq668
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq668
    | exact resolve eq668 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq674 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq671
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq671
    | exact resolve eq671 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq679 : (M.op x y) = (M.op (M.op x (M.op x y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16 x x
       have i₂ := eq674
       grind)
    | exact superpose eq674 eq16
    | exact resolve eq16 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq680 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq178 eq679
    | exact resolve eq679 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq685 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq680
       grind)
    | exact superpose eq680 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq694 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq672
       grind)
    | exact superpose eq672 eq37
    | exact resolve eq37 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq697 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq694
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq694
    | exact resolve eq694 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq719 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq685
       grind)
    | exact superpose eq685 eq41
    | exact resolve eq41 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq724 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq719
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq719
    | exact resolve eq719 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq726 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq724
    | exact resolve eq724 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq771 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (k X0 (σ y))) X0) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq661 eq16
    | exact resolve eq16 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq661 eq26
    | (have j1 := eq661 (σ x)
       grind)
    | exact resolve eq26 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq661 eq649
    | exact resolve eq649 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq661
  have eq778 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by grind
  clear eq775
  have eq784 : (σ y) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq662 eq774
    | exact resolve eq774 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq786 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (k X0 (σ y))) X0) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq589 eq771
    | exact resolve eq771 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq792 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (k X0 (σ y))) X0) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq662 eq786
    | exact resolve eq786 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq816 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq784 eq557
    | exact resolve eq557 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq819 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq784 eq91
    | exact resolve eq91 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq821 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq816
  have eq824 : y = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq32 eq819
    | exact resolve eq819 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq827 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq547 eq824
    | exact resolve eq824 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq833 : (M.op x x) = (M.op (M.op y x) y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq821
       grind)
    | exact superpose eq821 eq16
    | exact resolve eq16 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq835 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq821 eq833
    | exact resolve eq833 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821 eq833
  have eq838 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq835
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq835
    | exact resolve eq835 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq840 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq827
       grind)
    | exact superpose eq827 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq827
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq827
       grind)
    | exact resolve eq12 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : x = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq827
       grind)
    | exact superpose eq827 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : (M.op x x) = (M.op (M.op y x) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq827
       grind)
    | exact superpose eq827 eq16
    | exact resolve eq16 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq843 : y = (M.op y y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq840
  have eq844 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq827 eq842
    | exact resolve eq842 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq842
  have eq845 : y = (M.op x y) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq841
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq841
    | exact resolve eq841 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq846 : x = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq845
  have eq849 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq844
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq844
    | exact resolve eq844 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq850 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq838
       have i₂ := eq28 x x
       grind)
    | exact superpose eq28 eq838
    | (have j1 := eq28 x x
       grind)
    | exact resolve eq838 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq838
       grind)
    | exact superpose eq838 eq28
    | exact resolve eq28 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : (M.op x y) = (M.op (M.op x (M.op x y)) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16 x x
       have i₂ := eq838
       grind)
    | exact superpose eq838 eq16
    | exact resolve eq16 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq855 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq178 eq854
    | exact resolve eq854 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq856 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq853 eq850
    | exact resolve eq850 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq857 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq846
       grind)
    | exact superpose eq846 eq37
    | exact resolve eq37 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq860 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq857
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq857
    | exact resolve eq857 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq866 : (M.op x y) = (M.op (M.op x (M.op x y)) x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16 x x
       have i₂ := eq849
       grind)
    | exact superpose eq849 eq16
    | exact resolve eq16 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq867 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq178 eq866
    | exact resolve eq866 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq962 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq853
       grind)
    | exact superpose eq853 eq40
    | exact resolve eq40 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq965 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq962
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq962
    | exact resolve eq962 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq967 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq965
    | exact resolve eq965 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq1214 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq867
       have i₂ := eq843
       grind)
    | exact superpose eq843 eq867
    | exact resolve eq867 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843 eq867
  have eq1222 : x = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1214
  have eq1230 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1222
       grind)
    | exact superpose eq1222 eq41
    | exact resolve eq41 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1231 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1230
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1230
    | exact resolve eq1230 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1526 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1231 eq549
    | exact resolve eq549 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1545 : (M.op (σ x) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1526 eq16
    | exact resolve eq16 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1547 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1526 eq1545
    | exact resolve eq1545 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526 eq1545
  have eq1551 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1547
    | exact resolve eq1547 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547
  have eq1563 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1551 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1564 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1551 eq16
    | exact resolve eq16 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1565 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1563
  have eq1567 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq179 eq1564
    | exact resolve eq1564 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1601 : ∀ X0 X1 : G, (k X1 X1) = (M.op (M.op X0 (k X0 X1)) X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq541 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq541
    | (have j0 := eq541 X1 X1
       have j1 := eq28 X1 X1
       grind)
    | exact resolve eq541 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1655 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq551 X1
       have i₂ := eq541 X1 X0
       grind)
    | exact superpose eq541 eq551
    | (have j0 := eq551 X1
       have j1 := eq541 X1 X1
       grind)
    | exact resolve eq551 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1662 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1655 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655
  have eq1733 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1567 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq1567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567
  have eq1745 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq726 eq1733
    | exact resolve eq1733 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq1733
  have eq1749 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1745
       have r₂ := eq27
       grind)
    | exact resolve eq1745 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq1757 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1749 eq644
    | (have r₁ := eq644
       have r₂ := eq1749
       grind)
    | exact resolve eq644 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq1761 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1749
  have eq1764 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1757
  have eq1767 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq860 eq1764
    | exact resolve eq1764 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq1769 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1767
       have r₂ := eq1761
       grind)
    | exact resolve eq1767 eq1761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1761 eq1767
  have eq1801 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1769 eq1551
    | exact resolve eq1551 eq1769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551 eq1769
  have eq1810 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1801
  have eq2108 : (M.op (σ x) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq697 eq542
    | (have j0 := eq542 (σ y) (σ x)
       grind)
    | exact resolve eq542 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2117 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (k X0 (k X0 X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (M.op (k X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq542 X0 X1
       have i₂ := eq28 X0 (k X0 X1)
       grind)
    | exact superpose eq28 eq542
    | (have j0 := eq542 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | exact resolve eq542 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2156 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq2108
    | exact resolve eq2108 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2108
  have eq2157 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2156
  have eq2198 : (M.op (σ x) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1810 eq2157
    | exact resolve eq2157 eq1810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157
  have eq2501 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq784 eq792
    | exact resolve eq792 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq792
  have eq2547 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by grind
  clear eq2501
  have eq2560 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq2547
    | exact resolve eq2547 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2547
  have eq2567 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq662 eq2560
    | exact resolve eq2560 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq2560
  have eq2571 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq574 eq2567
    | exact resolve eq2567 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2567
  have eq2575 : (M.op x x) = (M.op (M.op y x) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq2571
       grind)
    | exact superpose eq2571 eq16
    | exact resolve eq16 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2580 : (k x x) = (M.op (M.op y x) y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq541 x y
       have i₂ := eq2571
       grind)
    | exact superpose eq2571 eq541
    | (have j0 := eq541 x x
       grind)
    | exact resolve eq541 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq2584 : (M.op x y) = (k x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2571 eq2580
    | exact resolve eq2580 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580
  have eq2589 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2571 eq2575
    | exact resolve eq2575 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2575
  have eq2593 : (M.op x y) = (k x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2584
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2584
    | exact resolve eq2584 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2584
  have eq2597 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2589
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2589
    | exact resolve eq2589 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2589
  have eq2604 : (M.op x y) = (M.op (M.op x (M.op x y)) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16 x x
       have i₂ := eq2597
       grind)
    | exact superpose eq2597 eq16
    | exact resolve eq16 eq2597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2605 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq2597
       grind)
    | exact superpose eq2597 eq28
    | exact resolve eq28 eq2597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597
  have eq2615 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq178 eq2604
    | exact resolve eq2604 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2604
  have eq2676 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq2605
       grind)
    | exact superpose eq2605 eq40
    | exact resolve eq40 eq2605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2605
  have eq2683 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2676
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2676
    | exact resolve eq2676 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676
  have eq2686 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq2683
    | exact resolve eq2683 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683
  have eq2735 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq2593
       grind)
    | exact superpose eq2593 eq40
    | exact resolve eq40 eq2593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2593
  have eq2746 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2735
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2735
    | exact resolve eq2735 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735
  have eq2749 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq2746
    | exact resolve eq2746 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2746
  have eq2752 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2686 eq2749
    | exact resolve eq2749 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq2757 : (τ (σ (M.op x y))) = (k x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2752 eq98
    | exact resolve eq98 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752
  have eq2771 : (M.op x y) = (k x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq2757
    | exact resolve eq2757 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757
  have eq3159 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq177 X0 (M.op X0 X0)
       have i₂ := eq16 X0 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3526 : (k (σ x) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq584 eq534
    | exact resolve eq534 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3547 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (M.op X1 (M.op X1 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq534 X1 X0
       grind)
    | exact superpose eq534 eq16
    | (have j1 := eq534 X1 X0
       grind)
    | exact resolve eq16 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq3586 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3547 X0 x
       have j1 := eq180 X0 X0 X0
       grind)
    | (have r₁ := eq3547 x X0
       have r₂ := eq180 X0 x x
       grind)
    | exact resolve eq3547 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq3547
  have eq3591 : (k (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq179 eq3526
    | exact resolve eq3526 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526
  have eq3639 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq3591
       have i₂ := eq3586 sF3
       grind)
    | exact superpose eq3586 eq3591
    | exact resolve eq3591 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3591
  have eq3666 : (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq179 eq3639
    | exact resolve eq3639 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3639
  have eq3686 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq3666
       have i₂ := eq3586 sF3
       grind)
    | exact superpose eq3586 eq3666
    | exact resolve eq3666 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666
  have eq3758 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3686 eq778
    | exact resolve eq778 eq3686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq3769 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq3686
  have eq3771 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq3758
  have eq3787 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq2571 eq3771
    | exact resolve eq3771 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3771
  have eq3794 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq3787
       have r₂ := eq3769
       grind)
    | exact resolve eq3787 eq3769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3769 eq3787
  have eq3797 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2571 eq3794
    | exact resolve eq3794 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571 eq3794
  have eq3815 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3797 eq587
    | exact resolve eq587 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq3827 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq3797 eq552
    | (have j0 := eq552 (σ x) X0
       grind)
    | (have r₁ := eq552 (σ x) x
       have r₂ := eq3797
       grind)
    | exact resolve eq552 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3797
  have eq3831 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq3827 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3827
  have eq3841 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3815
  have eq3858 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1810 eq3841
    | exact resolve eq3841 eq1810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3841
  have eq3868 : (M.op x x) = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3858 eq16
    | exact resolve eq16 eq3858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3872 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) x) (M.op x y))) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3858 eq176
    | exact resolve eq176 eq3858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3884 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x (M.op x y))) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3858 eq3872
    | exact resolve eq3872 eq3858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3872
  have eq3887 : (k x x) = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3868
       have i₂ := eq3586 x
       grind)
    | exact superpose eq3586 eq3868
    | exact resolve eq3868 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3868
  have eq3893 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3884
       have i₂ := eq16 sF0 x
       grind)
    | exact superpose eq16 eq3884
    | exact resolve eq3884 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3884
  have eq3896 : (k x x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3858 eq3887
    | exact resolve eq3887 eq3858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3887
  have eq3899 : (k (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3893
       have i₂ := eq3586 sF0
       grind)
    | exact superpose eq3586 eq3893
    | exact resolve eq3893 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893
  have eq4021 : (k x x) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3899 eq3896
    | exact resolve eq3896 eq3899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896
  have eq4035 : (k x x) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4021
  have eq4075 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq856
       have i₂ := eq4035
       grind)
    | exact superpose eq4035 eq856
    | exact resolve eq856 eq4035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq4081 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2771
       have i₂ := eq4035
       grind)
    | exact superpose eq4035 eq2771
    | exact resolve eq2771 eq4035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2771 eq4035
  have eq4089 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4081
  have eq4095 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4075
  have eq4117 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq551 (M.op x y)
       grind)
    | (have r₁ := eq4089
       have r₂ := eq551 (M.op x y)
       grind)
    | exact resolve eq4089 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4089
  have eq4119 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq551 (M.op x y)
       grind)
    | (have r₁ := eq4095
       have r₂ := eq551 (M.op x y)
       grind)
    | exact resolve eq4095 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq4095
  have eq4141 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4117
       have i₂ := eq3586 sF0
       grind)
    | exact superpose eq3586 eq4117
    | exact resolve eq4117 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4117
  have eq4144 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4119
       have i₂ := eq3586 sF0
       grind)
    | exact superpose eq3586 eq4119
    | exact resolve eq4119 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4119
  have eq4158 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4141 eq4144
    | exact resolve eq4144 eq4141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4141 eq4144
  have eq4159 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4158
  have eq4173 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4159 eq552
    | (have j0 := eq552 (M.op x y) X0
       grind)
    | (have r₁ := eq552 (M.op x y) x
       have r₂ := eq4159
       grind)
    | exact resolve eq552 eq4159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq4177 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4173 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4173
  have eq4354 : (M.op y y) = (M.op (k x (M.op x y)) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4177 eq178
    | exact resolve eq178 eq4177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4360 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4177 eq3899
    | exact resolve eq3899 eq4177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3899 eq4177
  have eq4379 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4360
  have eq4407 : (M.op x y) = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4159 eq4379
    | exact resolve eq4379 eq4159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4379
  have eq4412 : (k y y) = (M.op (k x (M.op x y)) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4354
       have i₂ := eq3586 y
       grind)
    | exact superpose eq3586 eq4354
    | exact resolve eq4354 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4354
  have eq4451 : (k (M.op x y) (M.op x y)) = (M.op (k x (M.op x y)) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1810 eq4412
    | exact resolve eq4412 eq1810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4412
  have eq4476 : (M.op x y) = (M.op (k x (M.op x y)) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4159 eq4451
    | exact resolve eq4451 eq4159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4159 eq4451
  have eq4491 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4407 eq4476
    | exact resolve eq4476 eq4407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4407 eq4476
  have eq4523 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4491 eq3858
    | exact resolve eq3858 eq4491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3858 eq4491
  have eq4535 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4523
  have eq4582 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4535 eq179
    | exact resolve eq179 eq4535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4535
  have eq4605 : (M.op (σ y) (σ y)) = (M.op (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4582
       have i₂ := eq3586 sF2
       grind)
    | exact superpose eq3586 eq4582
    | exact resolve eq4582 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4582
  have eq4609 : (k (σ y) (σ y)) = (M.op (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4605
       have i₂ := eq3586 sF3
       grind)
    | exact superpose eq3586 eq4605
    | exact resolve eq4605 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4605
  have eq5390 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3831 eq574
    | exact resolve eq574 eq3831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq3831
  have eq5391 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq5390
  have eq5414 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq860 eq5391
    | exact resolve eq5391 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq5391
  have eq6151 : (k (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq967 eq4609
    | exact resolve eq4609 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq6157 : (k (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2686 eq4609
    | exact resolve eq4609 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686 eq4609
  have eq6186 : (k (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq6157
  have eq6192 : (k (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6151
  have eq6211 : (k (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6186 eq6192
    | exact resolve eq6192 eq6186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6186 eq6192
  have eq6212 : (k (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq6211
  have eq6238 : (M.op (σ x) (σ x)) = (M.op (M.op (σ (M.op x y)) (k (σ y) (σ y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6212 eq16
    | exact resolve eq16 eq6212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6212
  have eq6261 : (k (σ x) (σ x)) = (M.op (M.op (σ (M.op x y)) (k (σ y) (σ y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq6238
       have i₂ := eq3586 sF2
       grind)
    | exact superpose eq3586 eq6238
    | exact resolve eq6238 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6238
  have eq6717 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 (k X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0
       have i₂ := eq3586 X0
       grind)
    | exact superpose eq3586 eq16
    | exact resolve eq16 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6735 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq855
       have i₂ := eq3586 y
       grind)
    | exact superpose eq3586 eq855
    | exact resolve eq855 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq6737 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2615
       have i₂ := eq3586 y
       grind)
    | exact superpose eq3586 eq2615
    | exact resolve eq2615 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2615
  have eq6743 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq584
       have i₂ := eq3586 sF2
       grind)
    | exact superpose eq3586 eq584
    | exact resolve eq584 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6749 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq589
       have i₂ := eq3586 sF3
       grind)
    | exact superpose eq3586 eq589
    | exact resolve eq589 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq6752 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6737 eq6735
    | exact resolve eq6735 eq6737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6735 eq6737
  have eq6753 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq6752
  have eq6781 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq6753
       grind)
    | exact superpose eq6753 eq41
    | exact resolve eq41 eq6753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6753
  have eq6789 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq6781
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6781
    | exact resolve eq6781 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6781
  have eq6793 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq6789
    | exact resolve eq6789 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6789
  have eq6846 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq6743 eq98
    | exact resolve eq98 eq6743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6743
  have eq6893 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq6749 eq116
    | exact resolve eq116 eq6749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq6901 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq6749 eq6793
    | exact resolve eq6793 eq6749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6749
  have eq6917 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq6901
       have r₂ := eq27
       grind)
    | exact resolve eq6901 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6901
  have eq6925 : (M.op x x) = (M.op (M.op y x) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq6917
       grind)
    | exact superpose eq6917 eq16
    | exact resolve eq16 eq6917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6948 : (k x x) = (M.op (M.op y x) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq6925
       have i₂ := eq3586 x
       grind)
    | exact superpose eq3586 eq6925
    | exact resolve eq6925 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6925
  have eq6960 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6917 eq6948
    | exact resolve eq6948 eq6917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6948
  have eq6970 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq6960
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6960
    | exact resolve eq6960 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6960
  have eq6991 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq6970
       grind)
    | exact superpose eq6970 eq40
    | exact resolve eq40 eq6970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6970
  have eq7004 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq6991
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6991
    | exact resolve eq6991 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6991
  have eq7009 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq7004
    | exact resolve eq7004 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7004
  have eq12828 : (k (σ x) (σ x)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6793 eq6261
    | exact resolve eq6261 eq6793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6261 eq6793
  have eq12859 : (k (σ x) (σ x)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq12828
  have eq12881 : (k (σ x) (σ x)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12859
       have i₂ := eq3586 sF1
       grind)
    | exact superpose eq3586 eq12859
    | exact resolve eq12859 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12859
  have eq12900 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7009 eq12881
    | exact resolve eq12881 eq7009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12881
  have eq12959 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12900 eq16
    | exact resolve eq16 eq12900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12993 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12959
       have i₂ := eq3586 sF1
       grind)
    | exact superpose eq3586 eq12959
    | exact resolve eq12959 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12959
  have eq13011 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12900 eq12993
    | exact resolve eq12993 eq12900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12993
  have eq13031 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13011 eq542
    | (have j0 := eq542 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq542 eq13011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq13011
  have eq13064 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13031
       have i₂ := eq3586 sF1
       grind)
    | exact superpose eq3586 eq13031
    | exact resolve eq13031 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13031
  have eq13075 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13064
       have i₂ := eq3586 sF1
       grind)
    | exact superpose eq3586 eq13064
    | exact resolve eq13064 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13064
  have eq13081 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12900 eq13075
    | exact resolve eq13075 eq12900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12900 eq13075
  have eq13082 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq13081
  have eq13098 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13082 eq164
    | exact resolve eq164 eq13082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq13082
  have eq13120 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq13098
    | exact resolve eq13098 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13098
  have eq18160 : (M.op (σ x) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2198
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq2198
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq2198 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2198
  have eq18200 : (k (σ x) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18160
       have i₂ := eq3586 sF2
       grind)
    | exact superpose eq3586 eq18160
    | exact resolve eq18160 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18160
  have eq18214 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq18200
    | exact resolve eq18200 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18200
  have eq18226 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq697 eq18214
    | exact resolve eq18214 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq18214
  have eq18236 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq18226
    | exact resolve eq18226 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18226
  have eq18246 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1565 eq18236
    | exact resolve eq18236 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565 eq18236
  have eq18247 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18246
  have eq18255 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1810 eq18247
    | exact resolve eq18247 eq1810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1810 eq18247
  have eq18298 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq18255 eq7009
    | exact resolve eq7009 eq18255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18255
  have eq18310 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq18298
  have eq18349 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18310 eq32
    | exact resolve eq32 eq18310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq18386 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18310 eq1231
    | exact resolve eq1231 eq18310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq18401 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18310 eq5414
    | exact resolve eq5414 eq18310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5414 eq18310
  have eq18421 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq18401
  have eq18435 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq18386
  have eq18450 : (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7009 eq18421
    | exact resolve eq18421 eq7009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18421
  have eq18451 : x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq18450
  have eq18466 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq18349
    | exact resolve eq18349 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18349
  have eq18477 : (M.op x y) = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq18466 eq29
    | exact resolve eq29 eq18466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18466
  have eq18500 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq18477
    | exact resolve eq18477 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18477
  have eq18542 : x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6917
       have i₂ := eq18500
       grind)
    | exact superpose eq18500 eq6917
    | exact resolve eq6917 eq18500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6917 eq18500
  have eq18562 : x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18451 eq18542
    | exact resolve eq18542 eq18451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18451 eq18542
  have eq18563 : x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq18562
  have eq18820 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18435 eq7009
    | exact resolve eq7009 eq18435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7009 eq18435
  have eq18832 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq18820
  have eq18869 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18832 eq29
    | exact resolve eq29 eq18832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18875 : (k y (M.op x y)) = (τ (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18832 eq117
    | exact resolve eq117 eq18832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq18879 : (k (M.op x y) (M.op x y)) = (τ (k (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18832 eq134
    | exact resolve eq134 eq18832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq18832
  have eq18883 : (k x x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq98 eq18879
    | exact resolve eq18879 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18879
  have eq18887 : (k y x) = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq115 eq18875
    | exact resolve eq18875 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq18875
  have eq18893 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq18869
    | exact resolve eq18869 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18869
  have eq18896 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq18893
       grind)
    | exact superpose eq18893 eq18
    | exact resolve eq18 eq18893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19165 : (M.op y y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18896 eq178
    | exact resolve eq178 eq18896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq18896
  have eq19208 : (k y y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19165
       have i₂ := eq3586 y
       grind)
    | exact superpose eq3586 eq19165
    | exact resolve eq19165 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19165
  have eq19223 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18893 eq19208
    | exact resolve eq19208 eq18893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19208
  have eq19284 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6846
       have i₂ := eq18883
       grind)
    | exact superpose eq18883 eq6846
    | exact resolve eq6846 eq18883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18883
  have eq19307 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18893 eq19284
    | exact resolve eq19284 eq18893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19284
  have eq19378 : x = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq603
       have i₂ := eq18887
       grind)
    | exact superpose eq18887 eq603
    | exact resolve eq603 eq18887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18887
  have eq19394 : (M.op x y) = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18893 eq19378
    | exact resolve eq19378 eq18893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19378
  have eq19402 : (M.op x y) = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18893 eq19394
    | exact resolve eq19394 eq18893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18893 eq19394
  have eq20205 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18563 eq19223
    | exact resolve eq19223 eq18563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18563 eq19223
  have eq20227 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq20205
  have eq20250 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13120 eq20227
    | exact resolve eq20227 eq13120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13120 eq20227
  have eq20251 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq20250
  have eq20273 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20251 eq29
    | exact resolve eq29 eq20251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20251
  have eq20306 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq20273
    | exact resolve eq20273 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20273
  have eq20307 : x = (M.op x y) := by grind
  clear eq20306
  have eq20312 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20307
       grind)
    | exact superpose eq20307 eq18
    | exact resolve eq18 eq20307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20313 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq20307
       grind)
    | exact superpose eq20307 eq22
    | exact resolve eq22 eq20307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq20315 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq20307
       grind)
    | exact superpose eq20307 eq40
    | exact resolve eq40 eq20307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq20317 : (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq547
       have i₂ := eq20307
       grind)
    | exact superpose eq20307 eq547
    | exact resolve eq547 eq20307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq20318 : (M.op x y) = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq603
       have i₂ := eq20307
       grind)
    | exact superpose eq20307 eq603
    | exact resolve eq603 eq20307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq20377 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq6846
       have i₂ := eq20307
       grind)
    | exact superpose eq20307 eq6846
    | exact resolve eq6846 eq20307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6846
  have eq20461 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20313 eq20
    | exact resolve eq20 eq20313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20592 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq20312 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20598 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op y y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq20312 eq177
    | exact resolve eq177 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq20609 : (k (M.op x y) (M.op x y)) = (M.op (M.op (k (M.op x y) (M.op x y)) (M.op y y)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq20598
       have i₂ := eq3586 sF0
       grind)
    | exact superpose eq3586 eq20598
    | exact resolve eq20598 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20598
  have eq20614 : y ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq20592
       have i₂ := eq3586 sF0
       grind)
    | exact superpose eq3586 eq20592
    | exact resolve eq20592 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20592
  have eq20617 : (k (M.op x y) (M.op x y)) = (M.op (M.op (k (M.op x y) (M.op x y)) (k y y)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq20609
       have i₂ := eq3586 y
       grind)
    | exact superpose eq3586 eq20609
    | exact resolve eq20609 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20609
  have eq21477 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20317 eq41
    | exact resolve eq41 eq20317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20317
  have eq21484 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20 eq21477
    | exact resolve eq21477 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21477
  have eq21490 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20461 eq21484
    | exact resolve eq21484 eq20461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21484
  have eq21687 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq21490 eq549
    | exact resolve eq549 eq21490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq21490
  have eq29804 : (k (M.op x y) (M.op x y)) = (M.op (M.op (k (M.op x y) (M.op x y)) (τ (M.op (σ x) (σ y)))) (k (M.op x y) (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq20617
       have i₂ := eq6893
       grind)
    | exact superpose eq6893 eq20617
    | exact resolve eq20617 eq6893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6893 eq20617
  have eq29855 : (M.op x y) = (M.op y (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op (k (M.op x y) (M.op x y)) (τ (M.op (σ x) (σ y)))) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq29804
       have i₂ := eq20307
       grind)
    | exact superpose eq20307 eq29804
    | exact resolve eq29804 eq20307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29804
  have eq29870 : (M.op x y) = (M.op y (M.op x y)) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq20377 eq29855
    | exact resolve eq29855 eq20377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20377 eq29855
  have eq29878 : (τ (M.op (σ x) (σ y))) = (M.op (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq29870
       have i₂ := eq3586 (τ sF4)
       grind)
    | exact superpose eq3586 eq29870
    | exact resolve eq29870 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29870
  have eq29884 : (τ (M.op (σ x) (σ y))) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq29878
       have i₂ := eq390 sF4 sF4
       grind)
    | exact superpose eq390 eq29878
    | exact resolve eq29878 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29878
  have eq29963 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq29884 eq16
    | exact resolve eq16 eq29884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29987 : (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq29963
       have i₂ := eq3586 (τ sF4)
       grind)
    | exact superpose eq3586 eq29963
    | exact resolve eq29963 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29963
  have eq29999 : (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq29987
       have i₂ := eq390 sF4 sF4
       grind)
    | exact superpose eq390 eq29987
    | exact resolve eq29987 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29987
  have eq30010 : (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq29884 eq29999
    | exact resolve eq29999 eq29884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29999
  have eq35847 : (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) (τ (M.op (σ x) (σ y)))) = (M.op (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) (τ (M.op (σ x) (σ y))))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq30010 eq176
    | exact resolve eq176 eq30010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35862 : (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) = (M.op (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y))))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq30010 eq35847
    | exact resolve eq35847 eq30010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30010 eq35847
  have eq35873 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq35862
       have i₂ := eq16 (τ sF4) (τ (k sF4 sF4))
       grind)
    | exact superpose eq16 eq35862
    | exact resolve eq35862 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35862
  have eq35882 : (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq35873
       have i₂ := eq3586 (τ sF4)
       grind)
    | exact superpose eq3586 eq35873
    | exact resolve eq35873 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35873
  have eq35889 : (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq35882
       have i₂ := eq390 sF4 sF4
       grind)
    | exact superpose eq390 eq35882
    | exact resolve eq35882 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq35882
  have eq35895 : (τ (M.op (σ x) (σ y))) = (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq29884 eq35889
    | exact resolve eq35889 eq29884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29884 eq35889
  have eq35910 : (σ (τ (M.op (σ x) (σ y)))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq35895 eq14
    | exact resolve eq14 eq35895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35895
  have eq35953 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq35910
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq35910
    | exact resolve eq35910 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35910
  have eq74278 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq584 eq3159
    | exact resolve eq3159 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq3159
  have eq74384 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x)))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq74278
       have i₂ := eq3586 sF4
       grind)
    | exact superpose eq3586 eq74278
    | exact resolve eq74278 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74278
  have eq74426 : (M.op x y) = (M.op y (M.op x y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x)))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq74384
       have i₂ := eq20307
       grind)
    | exact superpose eq20307 eq74384
    | exact resolve eq74384 eq20307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74384
  have eq74460 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq35953 eq74426
    | exact resolve eq74426 eq35953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35953 eq74426
  have eq100745 : (M.op (M.op x y) (M.op x y)) = (M.op (k y (M.op x y)) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20318 eq2117
    | (have j0 := eq2117 y (M.op x y)
       grind)
    | exact resolve eq2117 eq20318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20318
  have eq101041 : (M.op (M.op x y) (M.op x y)) = (M.op (k y (M.op x y)) y) ∨ y = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by grind
  clear eq100745
  have eq101142 : (k (M.op x y) (M.op x y)) = (M.op (k y (M.op x y)) y) ∨ y = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq101041
       have i₂ := eq3586 sF0
       grind)
    | exact superpose eq3586 eq101041
    | exact resolve eq101041 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101041
  have eq101354 : y = (M.op x y) ∨ (k (M.op x y) (M.op x y)) = (M.op (k y (M.op x y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20312 eq101142
    | exact resolve eq101142 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101142
  have eq101546 : y = (M.op x y) ∨ (τ (M.op (σ x) (σ y))) = (M.op (k y (M.op x y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq19307 eq101354
    | exact resolve eq101354 eq19307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19307 eq101354
  have eq101696 : y = (M.op x y) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq19402 eq101546
    | exact resolve eq101546 eq19402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19402 eq101546
  have eq101779 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20312 eq101696
    | exact resolve eq101696 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101696
  have eq101874 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq101779 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq101779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq101892 : (M.op x y) ≠ (M.op (M.op y (M.op x y)) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq101779 eq1662
    | (have j0 := eq1662 x (M.op x y)
       grind)
    | exact resolve eq1662 eq101779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101902 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) ≠ (M.op (M.op y (M.op x y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq101892
       have i₂ := eq3586 sF0
       grind)
    | exact superpose eq3586 eq101892
    | exact resolve eq101892 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101892
  have eq101921 : y = (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20312 eq101874
    | exact resolve eq101874 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101874
  have eq101922 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq101921
  have eq101928 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) ≠ (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq101779 eq101902
    | exact resolve eq101902 eq101779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101779 eq101902
  have eq101949 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq101928
       have r₂ := eq20312
       grind)
    | exact resolve eq101928 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101928
  have eq102030 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq101922 eq37
    | exact resolve eq37 eq101922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq101922
  have eq102065 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq102030
    | exact resolve eq102030 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102030
  have eq102088 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20461 eq102065
    | exact resolve eq102065 eq20461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102065
  have eq102168 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq101949 eq20315
    | exact resolve eq20315 eq101949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101949
  have eq102208 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq102168
    | exact resolve eq102168 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102168
  have eq102239 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20461 eq102208
    | exact resolve eq102208 eq20461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102208
  have eq102455 : (M.op (σ x) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq102088 eq2117
    | (have j0 := eq2117 (σ y) (σ x)
       grind)
    | exact resolve eq2117 eq102088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2117
  have eq102462 : (M.op (σ x) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq102455
  have eq102472 : (k (σ x) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq102462
       have i₂ := eq3586 sF2
       grind)
    | exact superpose eq3586 eq102462
    | exact resolve eq102462 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102462
  have eq102496 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq102472
    | exact resolve eq102472 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102472
  have eq102497 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq102496
  have eq102520 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq102088 eq102497
    | exact resolve eq102497 eq102088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102088 eq102497
  have eq102528 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq102520
    | exact resolve eq102520 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102520
  have eq102532 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102239 eq102528
    | exact resolve eq102528 eq102239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102239 eq102528
  have eq102566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102532 eq14
    | exact resolve eq14 eq102532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102532
  have eq102699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq102566
    | exact resolve eq102566 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102566
  have eq102721 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq102699
       have r₂ := eq27
       grind)
    | exact resolve eq102699 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102699
  have eq102741 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102721 eq179
    | exact resolve eq179 eq102721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq102742 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102721 eq182
    | exact resolve eq182 eq102721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq102836 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ x)))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102721 eq74460
    | exact resolve eq74460 eq102721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74460
  have eq102851 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq102886 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21687 eq102836
    | exact resolve eq102836 eq21687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102836
  have eq102950 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq102742
    | exact resolve eq102742 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102742
  have eq102951 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq102741
    | exact resolve eq102741 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102741
  have eq102963 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21687 eq102886
    | exact resolve eq102886 eq21687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102886
  have eq103008 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102950
       have i₂ := eq3586 sF3
       grind)
    | exact superpose eq3586 eq102950
    | exact resolve eq102950 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102950
  have eq103009 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102951
       have i₂ := eq3586 sF3
       grind)
    | exact superpose eq3586 eq102951
    | exact resolve eq102951 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102951
  have eq103016 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21687 eq102963
    | exact resolve eq102963 eq21687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21687 eq102963
  have eq103046 : (k (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103008
       have i₂ := eq3586 sF2
       grind)
    | exact superpose eq3586 eq103008
    | exact resolve eq103008 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103008
  have eq103047 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102721 eq103009
    | exact resolve eq103009 eq102721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103009
  have eq103050 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq103016
       have r₂ := eq102851
       grind)
    | exact resolve eq103016 eq102851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103016
  have eq103070 : (k (σ x) (σ x)) = (M.op (M.op (σ y) (k (σ y) (σ y))) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102721 eq103046
    | exact resolve eq103046 eq102721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102721 eq103046
  have eq103075 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103070
       have i₂ := eq6717 sF3
       grind)
    | exact superpose eq6717 eq103070
    | exact resolve eq103070 eq6717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6717 eq103070
  have eq103114 : (M.op (M.op y (M.op x y)) y) = (M.op (M.op (M.op x y) (M.op (M.op y (M.op x y)) y)) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103050 eq176
    | exact resolve eq176 eq103050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq103129 : (M.op x y) ≠ (M.op (M.op y (M.op x y)) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103050 eq1662
    | (have j0 := eq1662 x (M.op x y)
       grind)
    | exact resolve eq1662 eq103050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662
  have eq103139 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) ≠ (M.op (M.op y (M.op x y)) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103129
       have i₂ := eq3586 sF0
       grind)
    | exact superpose eq3586 eq103129
    | exact resolve eq103129 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103129
  have eq103155 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) (M.op (M.op x y) y)) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103050 eq103114
    | exact resolve eq103114 eq103050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103114
  have eq103166 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) ≠ (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103050 eq103139
    | exact resolve eq103139 eq103050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103050 eq103139
  have eq103182 : (M.op y y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103155
       have i₂ := eq16 y sF0
       grind)
    | exact superpose eq16 eq103155
    | exact resolve eq103155 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103155
  have eq103187 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq103166
       have r₂ := eq20312
       grind)
    | exact resolve eq103166 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103166
  have eq103201 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20312 eq103182
    | exact resolve eq103182 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20312 eq103182
  have eq103215 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103201
       have i₂ := eq3586 y
       grind)
    | exact superpose eq3586 eq103201
    | exact resolve eq103201 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103201
  have eq103394 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103187 eq20315
    | exact resolve eq20315 eq103187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20315 eq103187
  have eq103435 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq103394
    | exact resolve eq103394 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103394
  have eq103466 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20461 eq103435
    | exact resolve eq103435 eq20461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103435
  have eq103544 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq103215
       grind)
    | exact superpose eq103215 eq41
    | exact resolve eq41 eq103215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq103215
  have eq103581 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103544
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq103544
    | exact resolve eq103544 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103544
  have eq103603 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq103581
    | exact resolve eq103581 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103581
  have eq103620 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20461 eq103603
    | exact resolve eq103603 eq20461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103603
  have eq104027 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103620 eq1601
    | (have j0 := eq1601 (σ y) (σ y)
       grind)
    | exact resolve eq1601 eq103620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601 eq103620
  have eq104031 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq104027
  have eq104071 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104031
       have i₂ := eq3586 sF3
       grind)
    | exact superpose eq3586 eq104031
    | exact resolve eq104031 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104031
  have eq104095 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (k (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103047 eq104071
    | exact resolve eq104071 eq103047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103047 eq104071
  have eq104110 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (k (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103075 eq104095
    | exact resolve eq104095 eq103075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104095
  have eq104124 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103075 eq104110
    | exact resolve eq104110 eq103075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103075 eq104110
  have eq104135 : (σ x) = (σ y) ∨ (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103466 eq104124
    | exact resolve eq104124 eq103466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104124
  have eq104141 : (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq104135
       have r₂ := eq102851
       grind)
    | exact resolve eq104135 eq102851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102851 eq104135
  have eq104146 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103466 eq104141
    | exact resolve eq104141 eq103466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103466 eq104141
  have eq104151 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq104146
    | exact resolve eq104146 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104146
  have eq104152 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq104151
  have eq104161 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq104152 eq27
    | exact resolve eq27 eq104152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104152
  have eq104351 : y = (M.op x y) := by
    first
    | (have r₁ := eq104161
       have r₂ := eq20461
       grind)
    | exact resolve eq104161 eq20461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20461 eq104161
  have eq104410 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq104351
       grind)
    | exact superpose eq104351 eq24
    | exact resolve eq24 eq104351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq104469 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq20614
       have i₂ := eq104351
       grind)
    | exact superpose eq104351 eq20614
    | (have r₁ := eq20614
       have r₂ := eq104351
       grind)
    | exact resolve eq20614 eq104351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20614 eq104351
  have eq104524 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq104469
  have eq104525 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq104524
  have eq104600 : (σ x) = (σ y) := by
    first
    | exact superpose eq20313 eq104410
    | exact resolve eq104410 eq20313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20313 eq104410
  have eq104623 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq104600 eq26
    | exact resolve eq26 eq104600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq104600
  have eq104909 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq104623
       have i₂ := eq3586 sF2
       grind)
    | exact superpose eq3586 eq104623
    | exact resolve eq104623 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3586 eq104623
  have eq105209 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq104909 eq98
    | exact resolve eq98 eq104909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq104909
  have eq105301 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq105209
       have i₂ := eq20307
       grind)
    | exact superpose eq20307 eq105209
    | exact resolve eq105209 eq20307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20307 eq105209
  have eq105327 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq104525 eq105301
    | exact resolve eq105301 eq104525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104525 eq105301
  have eq105384 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105327 eq14
    | exact resolve eq14 eq105327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105327
  have eq105592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq105384
    | exact resolve eq105384 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq105384
  have eq105693 : False := by grind
  exact eq105693
