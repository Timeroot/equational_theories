import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) ≠ (M.op X0 (M.op X0 (M.op X1 X0))) ∨ (k X2 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op X2 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op X0 (M.op X1 X0)))
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X1 (M.op X2 X1)))
       have r₂ := eq9 (M.op X1 (M.op X1 (M.op X2 X1))) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op X2 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X0 (M.op X1 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq58 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq58 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq58 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq59 (σ X0)
       grind)
    | exact superpose eq59 eq15
    | exact resolve eq15 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq61
    | exact resolve eq61 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq61
  have eq84 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq96 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq70 X1
       grind)
    | exact superpose eq70 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq90
  have eq136 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X1 (M.op X2 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op X1 (M.op X1 (M.op X2 X1)))
       have i₂ := eq35 X1 X2 (τ X0)
       grind)
    | exact superpose eq35 eq17
    | exact resolve eq17 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq139 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X1 (M.op X2 X1))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq136 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136
    | exact resolve eq136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq164 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 (M.op X1 (M.op X2 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 (M.op X1 (M.op X2 X1))))
       have i₂ := eq139 (τ X0) X1 X2
       grind)
    | exact superpose eq139 eq17
    | exact resolve eq17 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq170 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op X1 (M.op X1 (M.op X2 X1)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq164 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq164
    | exact resolve eq164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq487 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq96 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq499 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq487 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq503 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq499 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq499 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq499 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq515 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq503 X0 X1
       have j1 := eq84 X1 (σ X0)
       grind)
    | (have r₁ := eq503 X0 X0
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq503 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq503
  have eq523 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq515 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq515
    | (have j0 := eq515 X0 X1
       grind)
    | exact resolve eq515 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq524 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq523 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq535 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq524 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq524
    | exact resolve eq524 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq543 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq524 x y
       grind)
    | exact superpose eq524 eq16
    | exact resolve eq16 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq617 : ∀ X0 X1 X2 X3 : G, (k (σ X1) X0) = (σ (k X1 (k (τ X0) (σ (M.op X2 (M.op X2 (M.op X3 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X0 (σ (M.op X2 (M.op X2 (M.op X3 X2)))) X1
       have i₂ := eq170 X0 X2 X3
       grind)
    | exact superpose eq170 eq22
    | exact resolve eq22 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq626 : ∀ X0 X1 X2 X3 : G, (k (σ X1) X0) = (M.op (σ X1) (k X0 (σ (σ (M.op X2 (M.op X2 (M.op X3 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq617 X0 X1 X2 X3
       have i₂ := eq535 X0 (σ (M.op X2 (M.op X2 (M.op X3 X2)))) X1
       grind)
    | exact superpose eq535 eq617
    | exact resolve eq617 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq617
  have eq639 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq626 X0 X1 x x
       have i₂ := eq170 X0 x x
       grind)
    | exact superpose eq170 eq626
    | exact resolve eq626 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq626
  have eq655 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq639
    | exact resolve eq639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq713 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq543
       have i₂ := eq655 x y
       grind)
    | exact superpose eq655 eq543
    | exact resolve eq543 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq655
  have eq714 : False := by grind
  exact eq714

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_y_pyx_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op X2 (M.op X3 X2))) (M.op (M.op X2 (M.op X2 (M.op X3 X2))) X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X2 (M.op X2 (M.op X3 X2))) X0
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) ≠ (M.op X0 (M.op X0 (M.op X1 X0))) ∨ (k X2 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op (M.op X0 (M.op X0 (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 (M.op X0 (M.op X1 X0)))
       have i₂ := eq14 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X1 (M.op X2 X1)))
       have r₂ := eq14 (M.op X1 (M.op X1 (M.op X2 X1))) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op (M.op X0 (M.op X0 (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
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
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  clear eq71
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
  clear eq37
  have eq223 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq127 eq51
    | exact resolve eq51 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq229 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f229_11 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 ∨ y = (M.op x y) := by
      intro X0
      grind
    have f229_16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
      intro X0 X1 X2
      grind
    have f229_17 : X0 ≠ (M.op X0 (σ y)) := by grind
    have f229_18 : y ≠ (M.op x y) := by grind
    have f229_20 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
      intro X0
      first
      | (have j0 := f229_11 X0
         grind)
      | (have r₁ := f229_11 X0
         have r₂ := f229_18
         grind)
      | exact resolve f229_11 f229_18
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f229_28 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
      intro X0
      first
      | (have i₁ := f229_16 X0 (σ y) (σ y)
         have i₂ := f229_20 (σ y)
         grind)
      | exact superpose f229_20 f229_16
      | exact resolve f229_16 f229_20
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f229_38 : X0 ≠ X0 := by
      first
      | (have i₁ := f229_17
         have i₂ := f229_28 X0
         grind)
      | exact superpose f229_28 f229_17
      | (have r₁ := f229_17
         have r₂ := f229_28 X0
         grind)
      | exact resolve f229_17 f229_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f229_39 : False := by grind
    exact f229_39
  clear eq223
  have eq235 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq229
    | (have j0 := eq229 (σ x)
       grind)
    | exact resolve eq229 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq229 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq229 (σ y)
       grind)
    | exact resolve eq13 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq242 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq236 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq268 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq235 eq127
    | exact resolve eq127 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq235
  have eq270 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq268
  have eq427 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq270 eq242
    | exact resolve eq242 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq270
  have eq434 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq427 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq553 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq434 eq118
    | exact resolve eq118 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq434
  have eq556 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq553
  have eq561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq556
    | exact resolve eq556 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq563 : y = (M.op x y) := by
    first
    | (have r₁ := eq561
       have r₂ := eq27
       grind)
    | exact resolve eq561 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq565 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq563 eq20
    | exact resolve eq20 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq565
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq565
    | exact resolve eq565 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq592 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op y (M.op x y))) (M.op (M.op y (M.op y (M.op x y))) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X1 X0 y x
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq637 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op y y)) (M.op (M.op y (M.op y y)) X1))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq563 eq592
    | exact resolve eq592 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq723 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq637 X0 (M.op (M.op y (M.op y y)) x)
       have i₂ := eq637 (M.op y (M.op y y)) x
       grind)
    | exact superpose eq637 eq637
    | exact resolve eq637 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq784 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq64 y y x
       have i₂ := eq723 y
       grind)
    | exact superpose eq723 eq64
    | exact resolve eq64 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq785 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq723 y
       grind)
    | exact superpose eq723 eq14
    | exact resolve eq14 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq815 : x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq785 x
       grind)
    | exact superpose eq785 eq18
    | (have j1 := eq785 x
       grind)
    | exact resolve eq18 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq823 : x = y := by
    first
    | exact superpose eq563 eq815
    | exact resolve eq815 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq830 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq823
       grind)
    | exact superpose eq823 eq24
    | exact resolve eq24 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq849 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq579 eq830
    | exact resolve eq830 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq858 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq849
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq849
    | exact resolve eq849 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq849
  have eq868 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq858 eq26
    | exact resolve eq26 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq895 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq579 eq868
    | exact resolve eq868 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq868
  have eq934 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq784 X0
       have i₂ := eq823
       grind)
    | exact superpose eq823 eq784
    | exact resolve eq784 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq823
  have eq943 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq934 sF0
       grind)
    | exact superpose eq934 eq137
    | exact resolve eq137 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq934
  have eq946 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq563 eq943
    | exact resolve eq943 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq943
  have eq950 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq858 eq946
    | exact resolve eq946 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858 eq946
  have eq953 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq950
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq950
    | exact resolve eq950 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq950
  have eq956 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq953
    | exact resolve eq953 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq953
  have eq961 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq956 eq92
    | (have j0 := eq92 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq92 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq956
  have eq962 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq961
  have eq964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq895 eq962
    | exact resolve eq962 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq962
  have eq967 : False := by grind
  exact eq967

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq61 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq62 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61
    | (have j0 := eq61 X0
       grind)
    | exact resolve eq61 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq82 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 (σ X0) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq57 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq57 X0
       grind)
    | exact resolve eq12 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq57 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq139 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq137 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq137 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq211 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq138 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq138
    | (have j0 := eq138 (τ X0)
       grind)
    | exact resolve eq138 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq138
  have eq212 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq211 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq211
    | (have j0 := eq211 X0
       grind)
    | exact resolve eq211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq217 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq212 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq212
    | (have j0 := eq212 X0
       grind)
    | exact resolve eq212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq224 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq217 (τ X0)
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq217
    | (have j0 := eq217 (τ X0)
       grind)
    | exact resolve eq217 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq574 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82
    | (have j0 := eq82 X1 X1
       grind)
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq608 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq574 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq574
    | (have j0 := eq574 X0 X1
       grind)
    | exact resolve eq574 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq657 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62
    | exact resolve eq62 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq672 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq657 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq657
    | (have j0 := eq657 X0
       grind)
    | exact resolve eq657 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq723 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ (τ (k X0 X0))) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq672 (τ X0)
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq672
    | (have j0 := eq672 (τ X0)
       grind)
    | exact resolve eq672 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq9135 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ (τ (k X0 X0))) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq723 X0
       grind)
    | exact superpose eq723 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq723 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq723 X0
       grind)
    | exact resolve eq12 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq9156 : ∀ X0 X1 : G, (τ (τ (k X0 X0))) = (τ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq9135 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9135
  have eq20688 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (τ (k (σ X0) (σ X0)))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9156 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9156
    | exact resolve eq9156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9156
  have eq20892 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k (τ (σ X0)) X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20688 X0 X1
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq20688
    | (have j0 := eq20688 X0 X1
       grind)
    | exact resolve eq20688 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20688
  have eq20914 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20892 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20892
    | (have j0 := eq20892 X0 X1
       grind)
    | exact resolve eq20892 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20892
  have eq21099 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq20914 X0 X1
       grind)
    | exact superpose eq20914 eq11
    | (have j1 := eq20914 X0 X1
       grind)
    | exact resolve eq11 eq20914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20914
  have eq21249 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21099 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq21099
    | (have j0 := eq21099 X0 X0
       grind)
    | exact resolve eq21099 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21099
  have eq21409 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21249 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21249
  have eq21410 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21409 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21409
  have eq21737 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 X1
       have i₂ := eq21410 X0
       grind)
    | exact superpose eq21410 eq139
    | (have j0 := eq139 X0 X1
       grind)
    | exact resolve eq139 eq21410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq21740 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq224 X0
       have i₂ := eq21410 X0
       grind)
    | exact superpose eq21410 eq224
    | (have j0 := eq224 X0
       grind)
    | exact resolve eq224 eq21410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq21796 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq21410 (σ X0)
       grind)
    | exact superpose eq21410 eq15
    | exact resolve eq15 eq21410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21805 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq21410 (τ X0)
       grind)
    | exact superpose eq21410 eq36
    | exact resolve eq36 eq21410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq21865 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq21805 X0
       have i₂ := eq21410 X0
       grind)
    | exact superpose eq21410 eq21805
    | exact resolve eq21805 eq21410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21805
  have eq21874 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq21796 X0
       have i₂ := eq21410 X0
       grind)
    | exact superpose eq21410 eq21796
    | exact resolve eq21796 eq21410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21410 eq21796
  have eq26542 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21740 (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq21740
    | (have j0 := eq21740 (σ X0)
       have j1 := eq84 X0 X1
       grind)
    | exact resolve eq21740 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq21740
  have eq26618 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26542 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26542
  have eq26692 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26618 X0 X1
       have i₂ := eq21865 (σ X0)
       grind)
    | exact superpose eq21865 eq26618
    | (have j0 := eq26618 X0 X1
       grind)
    | exact resolve eq26618 eq21865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21865 eq26618
  have eq26750 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26692 X0 X1
       have i₂ := eq21874 X0
       grind)
    | exact superpose eq21874 eq26692
    | (have j0 := eq26692 X0 X1
       grind)
    | exact resolve eq26692 eq21874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26692
  have eq26789 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26750 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq26750
    | (have j0 := eq26750 X0 X1
       grind)
    | exact resolve eq26750 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26750
  have eq26819 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26789 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26789
    | (have j0 := eq26789 X0 X1
       grind)
    | exact resolve eq26789 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26789
  have eq66978 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) X0)
       have i₂ := eq26819 X1 X0
       grind)
    | exact superpose eq26819 eq11
    | (have j1 := eq26819 X1 X0
       grind)
    | exact resolve eq11 eq26819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26819
  have eq67142 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66978 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq66978
    | (have j0 := eq66978 X0 X1
       grind)
    | exact resolve eq66978 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq66978
  have eq68249 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq67142 (σ X1) X0
       grind)
    | exact superpose eq67142 eq15
    | (have j1 := eq67142 (σ X1) X0
       grind)
    | exact resolve eq15 eq67142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67142
  have eq122278 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68249 x y
       grind)
    | exact superpose eq68249 eq16
    | (have j1 := eq68249 x y
       grind)
    | exact resolve eq16 eq68249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68249
  have eq123185 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq122278
       have i₂ := eq608 y x
       grind)
    | exact superpose eq608 eq122278
    | (have j1 := eq608 (σ x) (σ y)
       grind)
    | (have r₁ := eq122278
       have r₂ := eq608 y x
       grind)
    | (have r₁ := eq122278
       have r₂ := eq608 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq122278
       have r₂ := eq608 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq122278 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq122278
  have eq123186 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq123185
  have eq123187 : x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq123186
  have eq123193 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq123187
       grind)
    | exact superpose eq123187 eq16
    | exact resolve eq16 eq123187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123187
  have eq123194 : (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq123193
       have r₂ := eq21874 x
       grind)
    | exact resolve eq123193 eq21874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123193
  have eq123700 : y = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq123194
       grind)
    | exact superpose eq123194 eq10
    | exact resolve eq10 eq123194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123194
  have eq123884 : x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq123700
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq123700
    | exact resolve eq123700 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123700
  have eq123933 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq123884
       grind)
    | exact superpose eq123884 eq16
    | exact resolve eq16 eq123884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123884
  have eq123934 : x = (M.op x x) := by
    first
    | (have r₁ := eq123933
       have r₂ := eq21874 x
       grind)
    | exact resolve eq123933 eq21874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21874 eq123933
  have eq124449 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq123934
       grind)
    | exact superpose eq123934 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq123934
       grind)
    | exact resolve eq12 eq123934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124453 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq21737 x X0
       have i₂ := eq123934
       grind)
    | exact superpose eq123934 eq21737
    | (have j0 := eq21737 x X0
       grind)
    | exact resolve eq21737 eq123934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21737 eq123934
  have eq124581 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq124453 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124453
  have eq124583 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq124449 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124449
  have eq132995 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq124581 (σ X0)
       grind)
    | exact superpose eq124581 eq15
    | exact resolve eq15 eq124581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124581
  have eq133108 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq132995 X0
       have i₂ := eq124583 X0
       grind)
    | exact superpose eq124583 eq132995
    | exact resolve eq132995 eq124583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124583 eq132995
  have eq151313 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq133108 y
       grind)
    | exact superpose eq133108 eq16
    | (have r₁ := eq16
       have r₂ := eq133108 y
       grind)
    | exact resolve eq16 eq133108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133108
  have eq151573 : False := by grind
  exact eq151573

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_y_pxy_Equation443 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law443 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, (M.op X0 (M.op y (M.op y (M.op x y)))) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq95 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq99 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq95
  have eq100 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq99
  have eq725 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq77
  have eq763 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq725 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq725
    | (have j0 := eq725 x X0
       grind)
    | exact resolve eq725 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq6116 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq763 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq763
    | (have j0 := eq763 y
       grind)
    | exact resolve eq763 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq6162 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6116
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq6116
    | exact resolve eq6116 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6116
  have eq6195 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq6162
    | exact resolve eq6162 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6162
  have eq6203 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6195
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq6195
    | exact resolve eq6195 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6195
  have eq6208 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq6203
    | exact resolve eq6203 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6203
  have eq12192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq12192
    | exact resolve eq12192 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12192
  have eq12204 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq12193
       have r₂ := eq28
       grind)
    | exact resolve eq12193 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12193
  have eq12208 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq12204
    | exact resolve eq12204 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12204
  have eq12484 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq12208 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12208
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12208
       grind)
    | exact resolve eq12 eq12208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12208
  have eq15349 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq12484
    | (have j0 := eq12484 (σ x)
       grind)
    | (have r₁ := eq12484 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq12484 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12484
  have eq15350 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq15349
  have eq15351 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq15350
  have eq15360 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq15351 eq89
    | exact resolve eq89 eq15351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq15351
  have eq15373 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq15360
  have eq15801 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq15373
       grind)
    | exact superpose eq15373 eq100
    | exact resolve eq100 eq15373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq15811 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ y = (k X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq15373
       grind)
    | exact superpose eq15373 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15373
       grind)
    | exact resolve eq12 eq15373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15373
  have eq15834 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq15801
    | exact resolve eq15801 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15801
  have eq88582 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15811 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15811
    | (have j0 := eq15811 x
       grind)
    | (have r₁ := eq15811 x
       have r₂ := eq19
       grind)
    | exact resolve eq15811 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15811
  have eq88585 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq88582
  have eq88586 : y = (k x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq88585
  have eq88971 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq88586
       grind)
    | exact superpose eq88586 eq49
    | exact resolve eq49 eq88586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq88586
  have eq89057 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88971
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq88971
    | exact resolve eq88971 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88971
  have eq89113 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq89057 eq6208
    | exact resolve eq6208 eq89057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6208 eq89057
  have eq89168 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq89113
  have eq89213 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq89168 eq15834
    | exact resolve eq15834 eq89168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89168
  have eq89335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq89213
  have eq89349 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq89335
       have r₂ := eq28
       grind)
    | exact resolve eq89335 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89335
  have eq89763 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq89349 eq54
    | exact resolve eq54 eq89349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq89349
  have eq93825 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq89763 eq14
    | exact resolve eq14 eq89763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89763
  have eq94020 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq93825 eq15834
    | exact resolve eq15834 eq93825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15834 eq93825
  have eq94143 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq94020
  have eq94593 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq94143 eq30
    | exact resolve eq30 eq94143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94143
  have eq94730 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq94593
    | exact resolve eq94593 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq94593
  have eq94731 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq94730
  have eq94752 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq94731 eq30
    | exact resolve eq30 eq94731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq94731
  have eq95109 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq94752
    | exact resolve eq94752 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq94752
  have eq95130 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq95109 eq53
    | exact resolve eq53 eq95109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq102898 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq95130 y
       grind)
    | exact superpose eq95130 eq14
    | exact resolve eq14 eq95130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95130
  have eq103015 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq102898 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102898
    | (have j0 := eq102898 x
       grind)
    | exact resolve eq102898 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102898
  have eq103542 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq103015 eq95109
    | exact resolve eq95109 eq103015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95109 eq103015
  have eq103559 : x = y := by grind
  clear eq103542
  have eq104145 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq103559
       grind)
    | exact superpose eq103559 eq19
    | exact resolve eq19 eq103559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq104146 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq103559
       grind)
    | exact superpose eq103559 eq25
    | exact resolve eq25 eq103559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq103559
  have eq104410 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq104146
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq104146
    | exact resolve eq104146 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq104146
  have eq104440 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq104410 eq27
    | exact resolve eq27 eq104410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq104410
  have eq104691 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq104440 eq68
    | exact resolve eq68 eq104440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq104440
  have eq104723 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq104691
       have i₂ := eq104145
       grind)
    | exact superpose eq104145 eq104691
    | exact resolve eq104691 eq104145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104145 eq104691
  have eq104737 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq104723 eq15
    | exact resolve eq15 eq104723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104723
  have eq104994 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq104737
    | exact resolve eq104737 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq104737
  have eq105079 : False := by grind
  exact eq105079

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxx_x_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  clear eq24
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq77 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq77
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq172 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq211 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq55 X0 (M.op X0 x)
       have i₂ := eq55 X0 x
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq216 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
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
  have eq232 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq229 eq14
    | exact resolve eq14 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq232 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq232
    | exact resolve eq232 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq235 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq214 eq233
    | exact resolve eq233 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq371 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq214 eq211
    | exact resolve eq211 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq372 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq214 eq216
    | exact resolve eq216 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq520 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
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
  have eq521 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq214 eq520
    | exact resolve eq520 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq522 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq521 x x X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq521
    | exact resolve eq521 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq521
  have eq523 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq214 eq522
    | exact resolve eq522 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq532 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq523 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 x (M.op x (M.op x y))
       have r₂ := eq523 x
       grind)
    | exact resolve eq13 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq559 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (k X0 (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq372 X0 X0
       have i₂ := eq543 X0
       grind)
    | exact superpose eq543 eq372
    | exact resolve eq372 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq95 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq721 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq719 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq3311 : (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq543 eq721
    | (have j0 := eq721 (M.op x (M.op x y))
       grind)
    | exact resolve eq721 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3315 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq721 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq721
    | (have j0 := eq721 (τ X0)
       grind)
    | exact resolve eq721 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq721
  have eq3323 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3315 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3315
    | (have j0 := eq3315 X0
       grind)
    | exact resolve eq3315 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3315
  have eq3326 : (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq371 eq3311
    | exact resolve eq3311 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq3311
  have eq3327 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by grind
  clear eq3326
  have eq3331 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3323 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3323
    | (have j0 := eq3323 X0
       grind)
    | exact resolve eq3323 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3323
  have eq3334 : (σ (M.op x (M.op x y))) = (k (σ (M.op x (M.op x y))) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq3327
       have i₂ := eq543 (σ (M.op x sF0))
       grind)
    | exact superpose eq543 eq3327
    | exact resolve eq3327 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327
  have eq3460 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq172 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq172
    | (have j0 := eq172 x
       grind)
    | exact resolve eq172 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq3472 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3460
  have eq3482 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3472
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3472
    | exact resolve eq3472 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq3472
  have eq3500 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3482
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq3482 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3482
  have eq3507 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3500 eq49
    | exact resolve eq49 eq3500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3500
  have eq12602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq12603 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq12602
    | exact resolve eq12602 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12602
  have eq12614 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq12603
       have r₂ := eq27
       grind)
    | exact resolve eq12603 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12603
  have eq12616 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq12614
    | exact resolve eq12614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12614
  have eq12618 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq12616 eq3507
    | exact resolve eq3507 eq12616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3507 eq12616
  have eq12645 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq12618
    | exact resolve eq12618 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12618
  have eq12647 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3331 x
       grind)
    | (have r₁ := eq12645
       have r₂ := eq3331 x
       grind)
    | exact resolve eq12645 eq3331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3331 eq12645
  have eq12649 : x ≠ x ∨ x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq12647
       grind)
    | exact superpose eq12647 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq12647
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq12647
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq12647
       grind)
    | exact resolve eq13 eq12647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12647
  have eq12655 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12649
  have eq12677 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq720 x x
       have i₂ := eq12655
       grind)
    | exact superpose eq12655 eq720
    | (have j0 := eq720 x x
       grind)
    | exact resolve eq720 eq12655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12655
  have eq12680 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12677
  have eq12681 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12680
  have eq12691 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12681
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12681
    | exact resolve eq12681 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12681
  have eq12869 : (M.op (σ x) (σ x)) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12691 eq372
    | exact resolve eq372 eq12691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13353 : (σ x) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12869 eq12691
    | exact resolve eq12691 eq12869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12691 eq12869
  have eq13363 : (σ x) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13353
  have eq13382 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13363 eq235
    | exact resolve eq235 eq13363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13363
  have eq13407 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13382
    | exact resolve eq13382 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13382
  have eq13408 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13407
  have eq13414 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13408 eq229
    | exact resolve eq229 eq13408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq13417 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13414
    | exact resolve eq13414 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13414
  have eq13426 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13417 eq523
    | exact resolve eq523 eq13417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq13427 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13417 eq543
    | exact resolve eq543 eq13417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq13428 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k X0 (M.op (σ x) (σ y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13417 eq559
    | exact resolve eq559 eq13417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq13515 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13408 eq13426
    | exact resolve eq13426 eq13408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13426
  have eq13539 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13515 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13515
  have eq17555 : (σ (M.op (σ x) (σ y))) = (k (σ (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13417 eq3334
    | exact resolve eq3334 eq13417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334 eq13417
  have eq17596 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17555 eq13428
    | exact resolve eq13428 eq17555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13428
  have eq17608 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq17596
  have eq17689 : (M.op (σ x) (σ y)) = (k (σ (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17608 eq13427
    | exact resolve eq13427 eq17608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13427 eq17608
  have eq17699 : (M.op (σ x) (σ y)) = (k (σ (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq17689
  have eq17720 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17699 eq17555
    | exact resolve eq17555 eq17699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17555 eq17699
  have eq17741 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq17720
  have eq17913 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17741 eq16
    | exact resolve eq16 eq17741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17741
  have eq17965 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13408 eq17913
    | exact resolve eq17913 eq13408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13408 eq17913
  have eq18012 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) := by grind
  clear eq17965
  have eq18013 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq18012
    | exact resolve eq18012 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq18012
  have eq18244 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18013 eq13539
    | exact resolve eq13539 eq18013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13539 eq18013
  have eq18263 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18244 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18244
  have eq18903 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq18263 y
       grind)
    | exact superpose eq18263 eq18
    | (have j1 := eq18263 y
       grind)
    | exact resolve eq18 eq18263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18263
  have eq18974 : x = (M.op x y) := by grind
  clear eq18903
  have eq19074 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq18974 eq20
    | exact resolve eq20 eq18974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq19120 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18974 eq214
    | exact resolve eq214 eq18974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq19124 : (M.op x x) = (M.op (M.op x x) (σ y)) := by
    first
    | exact superpose eq18974 eq235
    | exact resolve eq235 eq18974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq19161 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19120
    | exact resolve eq19120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19120
  have eq19206 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19074
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19074
    | exact resolve eq19074 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19074
  have eq19207 : x = (M.op x x) := by
    first
    | exact superpose eq18974 eq19161
    | exact resolve eq19161 eq18974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19161
  have eq19245 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq19206 eq26
    | exact resolve eq26 eq19206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq19413 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq19207
       grind)
    | exact superpose eq19207 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq19207
       grind)
    | exact resolve eq13 eq19207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19419 : x = (k x x) := by grind
  clear eq19413
  have eq19469 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq720 x x
       have i₂ := eq19419
       grind)
    | exact superpose eq19419 eq720
    | (have j0 := eq720 x x
       grind)
    | exact resolve eq720 eq19419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq19419
  have eq19472 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq19469
  have eq19473 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq19472
  have eq19483 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19473
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19473
    | exact resolve eq19473 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq19473
  have eq19497 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq19206 eq19483
    | exact resolve eq19483 eq19206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19206 eq19483
  have eq19591 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq19497 eq372
    | exact resolve eq372 eq19497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq19596 : (M.op x x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq18974 eq19591
    | exact resolve eq19591 eq18974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18974 eq19591
  have eq19609 : (σ (M.op x y)) = (M.op x x) := by
    first
    | exact superpose eq19497 eq19596
    | exact resolve eq19596 eq19497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19497 eq19596
  have eq19621 : x = (σ (M.op x y)) := by
    first
    | (have i₁ := eq19609
       have i₂ := eq19207
       grind)
    | exact superpose eq19207 eq19609
    | exact resolve eq19609 eq19207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19609
  have eq19697 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq19621 eq19245
    | exact resolve eq19245 eq19621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19245
  have eq21584 : x = (M.op x (σ y)) := by
    first
    | (have i₁ := eq19124
       have i₂ := eq19207
       grind)
    | exact superpose eq19207 eq19124
    | exact resolve eq19124 eq19207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19124 eq19207
  have eq21585 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19697 eq21584
    | exact resolve eq21584 eq19697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19697 eq21584
  have eq21587 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq21585 eq27
    | exact resolve eq27 eq21585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq21585
  have eq21627 : False := by grind
  exact eq21627

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_pxy_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq208 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
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
  have eq220 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
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
  have eq221 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq208 eq220
    | exact resolve eq220 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq223 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq221 eq14
    | exact resolve eq14 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq223 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq223
    | exact resolve eq223 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq226 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq208 eq224
    | exact resolve eq224 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq249 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq381 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
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
  have eq399 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq221 eq381
    | exact resolve eq381 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq472 : ∀ X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq50 x x X2 X4 X5
       have i₂ := eq399 x x
       grind)
    | exact superpose eq399 eq50
    | exact resolve eq50 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq473 : ∀ X2 : G, (M.op x (M.op x y)) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq472 X2 x x
       have i₂ := eq399 x x
       grind)
    | exact superpose eq399 eq472
    | exact resolve eq472 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq486 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq473 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq473 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq486 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq500 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
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
  have eq501 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq208 eq500
    | exact resolve eq500 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq502 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq501 x x X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq501
    | exact resolve eq501 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq501
  have eq503 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq208 eq502
    | exact resolve eq502 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq502
  have eq542 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X0 X1 X2
       have i₂ := eq490 X0
       grind)
    | exact superpose eq490 eq14
    | exact resolve eq14 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq542 X0 x x
       have i₂ := eq399 x x
       grind)
    | exact superpose eq399 eq542
    | exact resolve eq542 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq601 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq76 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq606 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq601 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq610 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq606 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq606 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq606 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq3368 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq490 eq610
    | (have j0 := eq610 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq610 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq3384 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq473 eq3368
    | (have j0 := eq3368 X0
       grind)
    | exact resolve eq3368 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3368
  have eq3385 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq3384 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3384
  have eq3415 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3385 eq249
    | exact resolve eq249 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq3420 : (M.op (σ x) (σ x)) = (σ (k x (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3385 eq35
    | exact resolve eq35 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3421 : (M.op (σ y) (σ y)) = (σ (k y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3385 eq36
    | exact resolve eq36 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq3385
  have eq3445 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq490 eq3421
    | exact resolve eq3421 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421
  have eq3446 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq490 eq3420
    | exact resolve eq3420 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3420
  have eq3468 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq3445
       grind)
    | exact superpose eq3445 eq16
    | exact resolve eq16 eq3445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3445
  have eq3489 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq3446
       grind)
    | exact superpose eq3446 eq16
    | exact resolve eq16 eq3446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4121 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq490 eq3415
    | exact resolve eq3415 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq4126 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq3415 eq547
    | exact resolve eq547 eq3415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq3415
  have eq4203 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4121 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq4121
    | exact resolve eq4121 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4338 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (σ X0) (σ X0))
       have i₂ := eq4203 X0
       grind)
    | exact superpose eq4203 eq15
    | exact resolve eq15 eq4203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4203
  have eq4646 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1 X2
       have i₂ := eq4338 X0
       grind)
    | exact superpose eq4338 eq14
    | exact resolve eq14 eq4338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4649 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4646 X0 x x
       have i₂ := eq399 x x
       grind)
    | exact superpose eq399 eq4646
    | exact resolve eq4646 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4646
  have eq4987 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq503 eq4126
    | exact resolve eq4126 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4126
  have eq5014 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq4987
       have i₂ := eq4121 (M.op x sF0)
       grind)
    | exact superpose eq4121 eq4987
    | exact resolve eq4987 eq4121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4121 eq4987
  have eq5033 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq503 eq5014
    | exact resolve eq5014 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5014
  have eq5048 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq5033 eq15
    | exact resolve eq15 eq5033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28378 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq28379 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq28378
    | exact resolve eq28378 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28378
  have eq28390 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq28379
       have r₂ := eq27
       grind)
    | exact resolve eq28379 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28379
  have eq28394 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28390 eq3468
    | exact resolve eq3468 eq28390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468 eq28390
  have eq28436 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq28394
    | exact resolve eq28394 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28394
  have eq28437 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq28436
  have eq28447 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28437 eq3489
    | exact resolve eq3489 eq28437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3489 eq28437
  have eq28489 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq28447
    | exact resolve eq28447 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28447
  have eq28490 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq28489
  have eq28517 : (M.op y y) = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq399 y y
       have i₂ := eq28490
       grind)
    | exact superpose eq28490 eq399
    | exact resolve eq399 eq28490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28926 : y = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28490
       have i₂ := eq28517
       grind)
    | exact superpose eq28517 eq28490
    | exact resolve eq28490 eq28517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28490 eq28517
  have eq28940 : y = (M.op x (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq28926
  have eq28970 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28940 eq473
    | exact resolve eq473 eq28940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28986 : y = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28940 eq5048
    | exact resolve eq5048 eq28940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28940
  have eq29024 : x = (M.op x x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq28986
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28986
    | exact resolve eq28986 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28986
  have eq29362 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq3446
       have i₂ := eq29024
       grind)
    | exact superpose eq29024 eq3446
    | exact resolve eq3446 eq29024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29376 : (M.op x (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq4649 x
       have i₂ := eq29024
       grind)
    | exact superpose eq29024 eq4649
    | exact resolve eq4649 eq29024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29379 : (M.op x x) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq399 x x
       have i₂ := eq29024
       grind)
    | exact superpose eq29024 eq399
    | exact resolve eq399 eq29024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29392 : (σ (M.op x x)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq29376
       have i₂ := eq4338 x
       grind)
    | exact superpose eq4338 eq29376
    | exact resolve eq29376 eq4338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29376
  have eq29404 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq29362
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29362
    | exact resolve eq29362 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29362
  have eq29408 : (M.op (σ x) (σ x)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq29392
       have i₂ := eq3446
       grind)
    | exact superpose eq3446 eq29392
    | exact resolve eq29392 eq3446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29392
  have eq29592 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28970 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28970
    | (have j0 := eq28970 x
       grind)
    | exact resolve eq28970 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28970
  have eq29665 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3446
       have i₂ := eq29592
       grind)
    | exact superpose eq29592 eq3446
    | exact resolve eq3446 eq29592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29679 : (M.op x (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4649 x
       have i₂ := eq29592
       grind)
    | exact superpose eq29592 eq4649
    | exact resolve eq4649 eq29592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4649
  have eq29682 : (M.op x x) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq399 x x
       have i₂ := eq29592
       grind)
    | exact superpose eq29592 eq399
    | exact resolve eq399 eq29592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq29695 : (σ (M.op x x)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29679
       have i₂ := eq4338 x
       grind)
    | exact superpose eq4338 eq29679
    | exact resolve eq29679 eq4338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4338 eq29679
  have eq29707 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29665
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29665
    | exact resolve eq29665 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29665
  have eq29711 : (M.op (σ x) (σ x)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29695
       have i₂ := eq3446
       grind)
    | exact superpose eq3446 eq29695
    | exact resolve eq29695 eq3446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3446 eq29695
  have eq31015 : (σ x) = (M.op x (M.op x y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq29408 eq29404
    | exact resolve eq29404 eq29408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29404 eq29408
  have eq31033 : (σ x) = (M.op x (M.op x y)) ∨ y = (σ y) := by grind
  clear eq31015
  have eq31066 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq31033 eq226
    | exact resolve eq226 eq31033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31082 : (σ x) = (τ (σ x)) ∨ y = (σ y) := by
    first
    | exact superpose eq31033 eq5033
    | exact resolve eq5033 eq31033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31033
  have eq31127 : y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq28 eq31082
    | exact resolve eq31082 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31082
  have eq31130 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq26 eq31066
    | exact resolve eq31066 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31066
  have eq31133 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = (σ x) := by
    first
    | exact superpose eq31127 eq26
    | exact resolve eq26 eq31127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31218 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq31130 eq221
    | exact resolve eq221 eq31130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31130
  have eq31220 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq26 eq31218
    | exact resolve eq31218 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31218
  have eq31681 : (M.op (σ x) (σ y)) = (M.op x x) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq31220 eq29379
    | exact resolve eq29379 eq31220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29379 eq31220
  have eq31689 : (M.op (σ x) (σ y)) = (M.op x x) ∨ y = (σ y) := by grind
  clear eq31681
  have eq32022 : x = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq29024
       have i₂ := eq31689
       grind)
    | exact superpose eq31689 eq29024
    | exact resolve eq29024 eq31689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29024 eq31689
  have eq32041 : y = (σ y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq32022
  have eq32052 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32041 eq26
    | exact resolve eq26 eq32041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32041
  have eq38116 : (σ x) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29711 eq29707
    | exact resolve eq29707 eq29711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29707 eq29711
  have eq38136 : (σ x) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq38116
  have eq38174 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38136 eq226
    | exact resolve eq226 eq38136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq38190 : (σ x) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38136 eq5033
    | exact resolve eq5033 eq38136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5033 eq38136
  have eq38240 : y = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq28 eq38190
    | exact resolve eq38190 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq38190
  have eq38243 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq38174
    | exact resolve eq38174 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38174
  have eq38600 : (σ y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq38240 eq20
    | exact resolve eq20 eq38240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38655 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq38240 eq473
    | exact resolve eq473 eq38240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq38797 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq38655 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq38655
    | (have j0 := eq38655 X0
       grind)
    | exact resolve eq38655 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38655
  have eq38851 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq38600
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38600
    | exact resolve eq38600 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38600
  have eq38901 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38243 eq221
    | exact resolve eq221 eq38243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38243
  have eq38918 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq38901
    | exact resolve eq38901 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38901
  have eq38998 : y = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq38851 eq31127
    | exact resolve eq31127 eq38851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31127 eq38851
  have eq39001 : y = (σ (M.op x y)) ∨ x = (σ x) := by grind
  clear eq38998
  have eq41986 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (σ x) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq38240 eq38797
    | exact resolve eq38797 eq38240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38240 eq38797
  have eq42092 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq41986 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41986
  have eq42599 : (M.op (σ x) (σ y)) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38918 eq29682
    | exact resolve eq29682 eq38918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29682 eq38918
  have eq42612 : (M.op (σ x) (σ y)) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq42599
  have eq44804 : y = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | (have i₁ := eq31133
       have i₂ := eq42092 sF2
       grind)
    | exact superpose eq42092 eq31133
    | exact resolve eq31133 eq42092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31133 eq42092
  have eq44808 : y = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq44804
  have eq45210 : y ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq44808 eq27
    | exact resolve eq27 eq44808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44808
  have eq45232 : x = (σ x) := by
    first
    | (have r₁ := eq45210
       have r₂ := eq39001
       grind)
    | exact resolve eq45210 eq39001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39001 eq45210
  have eq45233 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq45232 eq26
    | exact resolve eq26 eq45232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq45321 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45232 eq32052
    | exact resolve eq32052 eq45232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32052
  have eq45336 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45321
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq45321
    | exact resolve eq45321 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45321
  have eq45960 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45336 eq27
    | exact resolve eq27 eq45336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45336
  have eq47536 : x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29592
       have i₂ := eq42612
       grind)
    | exact superpose eq42612 eq29592
    | exact resolve eq29592 eq42612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29592 eq42612
  have eq47557 : y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq47536
  have eq47690 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47557 eq5048
    | exact resolve eq5048 eq47557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5048 eq47557
  have eq47759 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq47690
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq47690
    | exact resolve eq47690 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47690
  have eq47870 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq47759
    | exact resolve eq47759 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47759
  have eq47936 : x = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq47870
       have r₂ := eq45960
       grind)
    | exact resolve eq47870 eq45960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45960 eq47870
  have eq48436 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq47936 eq27
    | exact resolve eq27 eq47936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq48437 : (M.op x (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq47936 eq221
    | exact resolve eq221 eq47936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq48468 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq45233 eq48437
    | exact resolve eq48437 eq45233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45233 eq48437
  have eq48469 : x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq47936 eq48468
    | exact resolve eq48468 eq47936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47936 eq48468
  have eq48488 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq48469 eq503
    | exact resolve eq503 eq48469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq48469
  have eq49239 : x = (M.op x y) := by
    first
    | (have i₁ := eq48488 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq48488
    | (have j0 := eq48488 y
       grind)
    | exact resolve eq48488 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq48488
  have eq49456 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq49239 eq20
    | exact resolve eq20 eq49239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq49239
  have eq49740 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq49456
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq49456
    | exact resolve eq49456 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq49456
  have eq49837 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq45232 eq49740
    | exact resolve eq49740 eq45232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45232 eq49740
  have eq49898 : False := by grind
  exact eq49898

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxx_pyx_pxy_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq91
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
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
  have eq215 : (M.op (M.op x y) y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq26
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
  have eq232 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq229 eq14
    | exact resolve eq14 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq232 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq232
    | exact resolve eq232 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq235 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq214 eq233
    | exact resolve eq233 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq236 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq214 eq215
    | exact resolve eq215 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
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
  clear eq229 eq391
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
  have eq558 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq214 eq553
    | exact resolve eq553 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq675 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq76 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq76 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq680 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq675 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq683 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq680 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq680 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq680 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq3364 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq506 eq683
    | (have j0 := eq683 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq683 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq3379 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq489 eq3364
    | (have j0 := eq3364 X0
       grind)
    | exact resolve eq3364 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364
  have eq3380 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq3379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3379
  have eq3410 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3380 eq259
    | exact resolve eq259 eq3380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq3416 : (M.op (σ y) (σ y)) = (σ (k y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3380 eq36
    | exact resolve eq36 eq3380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq3380
  have eq3439 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq506 eq3416
    | exact resolve eq3416 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3416
  have eq3463 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq3439
       grind)
    | exact superpose eq3439 eq16
    | exact resolve eq16 eq3439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3621 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq506 eq3410
    | exact resolve eq3410 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq3626 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq3410 eq558
    | exact resolve eq558 eq3410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq3410
  have eq3699 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3621 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3621
    | exact resolve eq3621 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3834 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (σ X0) (σ X0))
       have i₂ := eq3699 X0
       grind)
    | exact superpose eq3699 eq15
    | exact resolve eq15 eq3699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3699
  have eq4113 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq55 (σ X0) (σ X0)
       have i₂ := eq3834 X0
       grind)
    | exact superpose eq3834 eq55
    | exact resolve eq55 eq3834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4119 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq214 eq4113
    | exact resolve eq4113 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4113
  have eq4587 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq518 eq3626
    | exact resolve eq3626 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3626
  have eq4618 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq4587
       have i₂ := eq3621 (M.op x sF0)
       grind)
    | exact superpose eq3621 eq4587
    | exact resolve eq4587 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621 eq4587
  have eq4637 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq518 eq4618
    | exact resolve eq4618 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq4618
  have eq4650 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq4637 eq15
    | exact resolve eq15 eq4637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq29868 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq29867
    | exact resolve eq29867 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29867
  have eq29880 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq29868
       have r₂ := eq27
       grind)
    | exact resolve eq29868 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29868
  have eq29884 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29880 eq3463
    | exact resolve eq3463 eq29880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29880
  have eq29925 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq29884
    | exact resolve eq29884 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29884
  have eq29926 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq29925
  have eq29941 : (M.op x (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29926 eq411
    | exact resolve eq411 eq29926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29950 : (σ y) = (M.op x (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29941 eq29926
    | exact resolve eq29926 eq29941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29926 eq29941
  have eq29959 : (σ y) = (M.op x (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq29950
  have eq30301 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29959 eq235
    | exact resolve eq235 eq29959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq29959
  have eq62454 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30301 eq3463
    | exact resolve eq3463 eq30301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3463 eq30301
  have eq62495 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq62454
    | exact resolve eq62454 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62454
  have eq62496 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq62495
  have eq62506 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3439
       have i₂ := eq62496
       grind)
    | exact superpose eq62496 eq3439
    | exact resolve eq3439 eq62496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62519 : (M.op x (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4119 y
       have i₂ := eq62496
       grind)
    | exact superpose eq62496 eq4119
    | exact resolve eq4119 eq62496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4119
  have eq62526 : (M.op y y) = (M.op x (M.op x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq411 y y
       have i₂ := eq62496
       grind)
    | exact superpose eq62496 eq411
    | exact resolve eq411 eq62496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62535 : (M.op x (M.op x y)) = (σ (M.op y y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq62519
       have i₂ := eq3834 y
       grind)
    | exact superpose eq3834 eq62519
    | exact resolve eq62519 eq3834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3834 eq62519
  have eq62547 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq62506
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq62506
    | exact resolve eq62506 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62506
  have eq62551 : (M.op x (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq62535
       have i₂ := eq3439
       grind)
    | exact superpose eq3439 eq62535
    | exact resolve eq62535 eq3439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439 eq62535
  have eq62993 : y = (M.op x (M.op x y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq62496
       have i₂ := eq62526
       grind)
    | exact superpose eq62526 eq62496
    | exact resolve eq62496 eq62526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62496 eq62526
  have eq63009 : y = (M.op y x) ∨ y = (M.op x (M.op x y)) := by grind
  clear eq62993
  have eq63820 : (σ y) = (M.op x (M.op x y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq62551 eq62547
    | exact resolve eq62547 eq62551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62547 eq62551
  have eq63836 : (σ y) = (M.op x (M.op x y)) ∨ y = (M.op y x) := by grind
  clear eq63820
  have eq63878 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq63836 eq489
    | exact resolve eq489 eq63836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63895 : (σ y) = (τ (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq63836 eq4637
    | exact resolve eq4637 eq63836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4637 eq63836
  have eq63945 : y = (M.op y x) ∨ y = (σ y) := by
    first
    | exact superpose eq29 eq63895
    | exact resolve eq63895 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq63895
  have eq64327 : (M.op y x) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq411 y x
       have i₂ := eq63945
       grind)
    | exact superpose eq63945 eq411
    | exact resolve eq411 eq63945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63945
  have eq64731 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq63878
    | (have j0 := eq63878 (σ x)
       grind)
    | exact resolve eq63878 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63878
  have eq64822 : (M.op y x) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq411 y x
       have i₂ := eq64731
       grind)
    | exact superpose eq64731 eq411
    | exact resolve eq411 eq64731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq64731
  have eq65706 : y = (M.op x (M.op x y)) ∨ y = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq63009
       have i₂ := eq64327
       grind)
    | exact superpose eq64327 eq63009
    | exact resolve eq63009 eq64327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64327
  have eq65716 : y = (M.op x (M.op x y)) ∨ y = (σ y) := by grind
  clear eq65706
  have eq65751 : y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq65716 eq4650
    | exact resolve eq4650 eq65716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4650 eq65716
  have eq65801 : y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq65751
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq65751
    | exact resolve eq65751 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65751
  have eq65802 : y = (σ y) := by grind
  clear eq65801
  have eq65809 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq65802 eq26
    | exact resolve eq26 eq65802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq72416 : (M.op y x) = (M.op x (M.op x y)) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65802 eq64822
    | exact resolve eq64822 eq65802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64822
  have eq72971 : y = (M.op x (M.op x y)) ∨ y = (M.op x (M.op x y)) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63009
       have i₂ := eq72416
       grind)
    | exact superpose eq72416 eq63009
    | exact resolve eq63009 eq72416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63009 eq72416
  have eq72983 : y = (M.op x (M.op x y)) ∨ y = (M.op (σ x) (σ y)) := by grind
  clear eq72971
  have eq73007 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq72983 eq489
    | exact resolve eq489 eq72983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq72983
  have eq73719 : y = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65809
       have i₂ := eq73007 sF2
       grind)
    | exact superpose eq73007 eq65809
    | exact resolve eq65809 eq73007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73007
  have eq73722 : y = (M.op (σ x) (σ y)) := by grind
  clear eq73719
  have eq73784 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq73722 eq27
    | exact resolve eq27 eq73722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq73788 : (M.op x (M.op x y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq73722 eq236
    | exact resolve eq236 eq73722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq73790 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq65809 eq73788
    | exact resolve eq73788 eq65809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65809 eq73788
  have eq73793 : y = (M.op x (M.op x y)) := by
    first
    | exact superpose eq73722 eq73790
    | exact resolve eq73790 eq73722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73722 eq73790
  have eq74396 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq73793 eq55
    | exact resolve eq55 eq73793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq74400 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq214 eq74396
    | exact resolve eq74396 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq74396
  have eq74423 : y = (M.op x y) := by
    first
    | exact superpose eq73793 eq74400
    | exact resolve eq74400 eq73793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73793 eq74400
  have eq74433 : y = (M.op x y) := by
    first
    | (have i₁ := eq74423
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74423
    | exact resolve eq74423 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq74423
  have eq74440 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq74433 eq20
    | exact resolve eq20 eq74433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq74433
  have eq74780 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq74440
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq74440
    | exact resolve eq74440 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq74440
  have eq74942 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq65802 eq74780
    | exact resolve eq74780 eq65802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65802 eq74780
  have eq75025 : False := by grind
  exact eq75025

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pyx_Equation4430 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq57 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 (M.op x x) x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq210 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq58 X0 (M.op X0 x)
       have i₂ := eq58 X0 x
       grind)
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq58 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 x y
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq59 x x
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq59
    | exact resolve eq59 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq226 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq213 eq225
    | exact resolve eq225 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq228 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq226 eq14
    | exact resolve eq14 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq229 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq228 x x
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq228
    | exact resolve eq228 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq231 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq213 eq229
    | exact resolve eq229 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq396 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq58 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq58
    | exact resolve eq58 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq397 X0 x x
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq397
    | exact resolve eq397 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq401 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq213 eq396
    | exact resolve eq396 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq402 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq213 eq400
    | exact resolve eq400 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq403 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq213 eq210
    | exact resolve eq210 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq547 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq57 x x X2 X3 X5
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq57
    | exact resolve eq57 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq548 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq213 eq547
    | exact resolve eq547 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq549 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq548 x x X5
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq548
    | exact resolve eq548 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq548
  have eq550 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq213 eq549
    | exact resolve eq549 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq549
  have eq998 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq550 eq401
    | exact resolve eq401 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq1025 : (M.op x (M.op x y)) = (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq998
       have i₂ := eq45 (M.op x sF0)
       grind)
    | exact superpose eq45 eq998
    | exact resolve eq998 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1041 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq403 eq1025
    | exact resolve eq1025 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403 eq1025
  have eq1121 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq1041 eq16
    | exact resolve eq16 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq10957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (M.op (σ x) (σ x)) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq10958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq10957
    | exact resolve eq10957 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10957
  have eq10969 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq10958
       have r₂ := eq28
       grind)
    | exact resolve eq10958 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10958
  have eq10975 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq10969 eq72
    | exact resolve eq72 eq10969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10969
  have eq11009 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq10975
    | exact resolve eq10975 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10975
  have eq11010 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11009
  have eq11018 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq11010
       grind)
    | exact superpose eq11010 eq52
    | exact resolve eq52 eq11010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11028 : (M.op x (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq402 x
       have i₂ := eq11010
       grind)
    | exact superpose eq11010 eq402
    | exact resolve eq402 eq11010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq11010
  have eq11044 : (σ (M.op x x)) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11028
       have i₂ := eq45 x
       grind)
    | exact superpose eq45 eq11028
    | exact resolve eq11028 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq11028
  have eq11053 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11018
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11018
    | exact resolve eq11018 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11018
  have eq11055 : (M.op (σ x) (σ x)) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11044
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq11044
    | exact resolve eq11044 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq11044
  have eq11403 : (σ x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11055 eq11053
    | exact resolve eq11053 eq11055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11053 eq11055
  have eq11415 : (σ x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11403
  have eq11561 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11415 eq231
    | exact resolve eq231 eq11415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq11563 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11415 eq550
    | exact resolve eq550 eq11415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq11566 : (σ x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11415 eq1121
    | exact resolve eq1121 eq11415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121 eq11415
  have eq11599 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq11566
    | exact resolve eq11566 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11566
  have eq11600 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq11561
    | exact resolve eq11561 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11561
  have eq11605 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq11599 eq30
    | exact resolve eq30 eq11599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11599
  have eq11721 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq11605
    | exact resolve eq11605 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11605
  have eq11722 : x = (σ x) ∨ x = y := by grind
  clear eq11721
  have eq11742 : x = (τ x) ∨ x = y := by
    first
    | exact superpose eq11722 eq29
    | exact resolve eq29 eq11722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq11997 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11600 eq28
    | exact resolve eq28 eq11600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11600
  have eq12892 : ∀ X0 : G, x = (M.op x X0) ∨ x = (σ y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq11722 eq11563
    | exact resolve eq11563 eq11722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11563 eq11722
  have eq12937 : ∀ X0 : G, x = (M.op x X0) ∨ x = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq12892 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12892
  have eq13636 : x = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12937 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12937
    | (have j0 := eq12937 y
       grind)
    | exact resolve eq12937 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12937
  have eq13755 : y = (τ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13636 eq30
    | exact resolve eq30 eq13636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13636
  have eq13857 : x = y ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11742
       have i₂ := eq13755
       grind)
    | exact superpose eq13755 eq11742
    | exact resolve eq11742 eq13755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11742 eq13755
  have eq13892 : x = (M.op x y) ∨ x = y := by grind
  clear eq13857
  have eq13904 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq13892 eq21
    | exact resolve eq21 eq13892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14037 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq13904
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13904
    | exact resolve eq13904 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13904
  have eq14129 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14037 eq11997
    | (have r₁ := eq11997
       have r₂ := eq14037
       grind)
    | exact resolve eq11997 eq14037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11997 eq14037
  have eq14134 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq14129
  have eq14135 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq14134
  have eq14231 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq14135 eq30
    | exact resolve eq30 eq14135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14135
  have eq14368 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq14231
    | exact resolve eq14231 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14231
  have eq14538 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14368 eq13892
    | exact resolve eq13892 eq14368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13892 eq14368
  have eq14539 : x = y := by grind
  clear eq14538
  have eq14641 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq14539
       grind)
    | exact superpose eq14539 eq19
    | exact resolve eq19 eq14539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq14642 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq14539
       grind)
    | exact superpose eq14539 eq25
    | exact resolve eq25 eq14539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq14539
  have eq14748 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14642
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14642
    | exact resolve eq14642 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14642
  have eq14765 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14748 eq27
    | exact resolve eq27 eq14748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14748
  have eq14999 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq14765 eq72
    | exact resolve eq72 eq14765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq14765
  have eq15035 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14999
       have i₂ := eq14641
       grind)
    | exact superpose eq14641 eq14999
    | exact resolve eq14999 eq14641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14641 eq14999
  have eq15049 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15035 eq15
    | exact resolve eq15 eq15035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15035
  have eq15097 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq15049
    | exact resolve eq15049 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq15049
  have eq15106 : False := by grind
  exact eq15106
