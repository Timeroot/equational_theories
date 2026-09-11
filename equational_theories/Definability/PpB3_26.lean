import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pyx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq21 X0 X1 X2
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | (have r₁ := eq12 X0 (M.op X0 (M.op (M.op X1 X1) X0))
       have r₂ := eq21 X0 X1 (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = X3 ∨ (M.op X3 X3) = X3 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3
       have i₂ := eq21 X0 X1 X2
       grind)
    | exact superpose eq21 eq14
    | (have j0 := eq14 X3 X3
       grind)
    | exact resolve eq14 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq21 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq108 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = X3 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq99 X0 X1 X2 X3
       have j1 := eq12 X2 X3
       grind)
    | (have r₁ := eq99 X0 X1 X2 (M.op (M.op X0 (M.op (M.op X1 X1) X0)) (M.op X0 (M.op (M.op X1 X1) X0)))
       have r₂ := eq12 X0 (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | (have r₁ := eq99 X0 X1 X2 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq99 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq110 : ∀ X0 X2 X3 : G, (M.op X0 X0) ≠ X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq97 X0 x X2 X3
       have i₂ := eq105 x X0
       grind)
    | exact superpose eq105 eq97
    | (have j0 := eq97 X0 x X2 X3
       grind)
    | (have r₁ := eq97 (M.op X0 X0) x (M.op (M.op x x) (M.op X0 X0)) X3
       have r₂ := eq105 X0 (M.op (M.op x x) (M.op X0 X0))
       grind)
    | (have r₁ := eq97 X0 x (M.op (M.op X0 X0) (M.op X0 (M.op (M.op x x) X0))) X3
       have r₂ := eq105 X0 (M.op X0 (M.op (M.op x x) X0))
       grind)
    | exact resolve eq97 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq122 : ∀ X0 X2 X3 : G, (M.op X0 X0) = X3 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq108 X0 x X2 X3
       have i₂ := eq105 x X0
       grind)
    | exact superpose eq105 eq108
    | (have j0 := eq108 X0 x X2 X3
       grind)
    | exact resolve eq108 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq108
  have eq127 : ∀ X2 X3 : G, (M.op X2 X3) = (k X2 X3) := by
    intro X2 X3
    first
    | (have j0 := eq122 x X2 X3
       have j1 := eq110 x X3 X2
       grind)
    | (have r₁ := eq122 x X2 X2
       have r₂ := eq110 x X2 X3
       grind)
    | (have r₁ := eq122 x X2 (M.op x x)
       have r₂ := eq110 x (M.op x x) X3
       grind)
    | (have r₁ := eq122 x x x
       have r₂ := eq110 x (k x x) X3
       grind)
    | exact resolve eq122 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq122
  have eq430 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq127 (σ X0) (σ X1)
       grind)
    | exact superpose eq127 eq15
    | exact resolve eq15 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq430 X0 X1
       have i₂ := eq127 X0 X1
       grind)
    | exact superpose eq127 eq430
    | exact resolve eq430 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq430
  have eq438 : False := by grind
  exact eq438

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq40 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq40 X1 X0
       grind)
    | (have r₁ := eq49 X1 X0
       have r₂ := eq40 X0 X1
       grind)
    | exact resolve eq49 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq49
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq52
  have eq160 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq164 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq160 X0 X1
       have j1 := eq54 X0 X1
       grind)
    | (have r₁ := eq160 X0 X1
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq160 X1 X1
       have r₂ := eq54 X1 X1
       grind)
    | exact resolve eq160 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq160
  have eq457 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq164 (σ X0) (σ X1)
       grind)
    | exact superpose eq164 eq15
    | exact resolve eq15 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 X1
       have i₂ := eq164 X0 X1
       grind)
    | exact superpose eq164 eq457
    | exact resolve eq457 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq457
  have eq465 : False := by grind
  exact eq465

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq62 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq99 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X1 X1) X2
       have i₂ := eq73 X1 X0
       grind)
    | exact superpose eq73 eq9
    | exact resolve eq9 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq99 (M.op X0 (M.op X1 X1)) X3 x
       have i₂ := eq99 X0 x X1
       grind)
    | exact superpose eq99 eq99
    | exact resolve eq99 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq65 X0 X1
       grind)
    | (have i₁ := eq12 X2 X1
       have i₂ := eq65 X1 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X2 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq65 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq65 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq73 X0 (M.op X0 X0)
       grind)
    | exact superpose eq73 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq73 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq219 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq236 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = (τ (M.op (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq223 X1 (σ X0)
       grind)
    | exact superpose eq223 eq28
    | exact resolve eq28 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = (σ (M.op (τ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq223 X1 (τ X0)
       grind)
    | exact superpose eq223 eq17
    | exact resolve eq17 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 X2 : G, (τ (M.op (σ X0) (M.op X1 X1))) = (k X0 (τ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq236 X0 X2
       have i₂ := eq112 (σ X0) X1 X2
       grind)
    | (have i₁ := eq236 X0 X2
       have i₂ := eq112 (σ X0) X2 X1
       grind)
    | exact superpose eq112 eq236
    | exact resolve eq236 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq279 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (M.op X1 X1))) = (k X0 (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq237 X0 X2
       have i₂ := eq112 (τ X0) X1 X2
       grind)
    | (have i₁ := eq237 X0 X2
       have i₂ := eq112 (τ X0) X2 X1
       grind)
    | exact superpose eq112 eq237
    | exact resolve eq237 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq319 : ∀ X0 X1 X2 : G, (τ (M.op (σ (τ X0)) (M.op X1 X1))) = (τ (k X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (M.op X2 X2) X0
       have i₂ := eq258 (τ X0) X1 X2
       grind)
    | exact superpose eq258 eq31
    | exact resolve eq31 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq320 : ∀ X0 X1 X2 : G, (k X0 (σ (τ (M.op X2 X2)))) = (σ (τ (M.op (σ (τ X0)) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (τ (M.op X2 X2))
       have i₂ := eq258 (τ X0) X1 X2
       grind)
    | exact superpose eq258 eq17
    | exact resolve eq17 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op X1 X1)) = (k X0 (σ (τ (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq320 X0 X1 X2
       have i₂ := eq11 (M.op (σ (τ X0)) (M.op X1 X1))
       grind)
    | exact superpose eq11 eq320
    | exact resolve eq320 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq324 : ∀ X0 X1 X2 : G, (τ (M.op (σ (τ X0)) (M.op X1 X1))) = (τ (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq319 X0 X1 X2
       have i₂ := eq223 X2 X0
       grind)
    | exact superpose eq223 eq319
    | exact resolve eq319 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq319
  have eq333 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op X1 X1)) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq323 X0 X1 X2
       have i₂ := eq11 (M.op X2 X2)
       grind)
    | exact superpose eq11 eq323
    | exact resolve eq323 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq334 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X1 X1))) = (τ (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq324
    | exact resolve eq324 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq338 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq333 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq333
    | exact resolve eq333 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq351 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq338 (M.op X1 X1) X1 X2
       have i₂ := eq65 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq338 (M.op X1 X1) X1 X2
       have i₂ := eq65 (M.op X1 X1) X0
       grind)
    | exact superpose eq65 eq338
    | exact resolve eq338 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 X1 X2 : G, (σ (k (τ X0) (M.op X1 X1))) = (k X0 (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq237 X0 X2
       have i₂ := eq338 (τ X0) X2 X1
       grind)
    | exact superpose eq338 eq237
    | exact resolve eq237 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq386 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 X1))) = (k X0 (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq383 X0 X1 X2
       have i₂ := eq17 X0 (M.op X1 X1)
       grind)
    | exact superpose eq17 eq383
    | exact resolve eq383 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq383
  have eq817 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (τ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq334 (M.op X1 X1) X2 X0
       have i₂ := eq73 X1 (M.op X0 X0)
       grind)
    | exact superpose eq73 eq334
    | exact resolve eq334 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq817 X0 x X2
       have i₂ := eq73 x (M.op X2 X2)
       grind)
    | exact superpose eq73 eq817
    | exact resolve eq817 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq979 : ∀ X0 X1 X2 : G, (k (σ X0) (σ (M.op X1 X1))) = (σ (k X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 (M.op X2 X2)
       have i₂ := eq386 (σ X0) X2 X1
       grind)
    | (have i₁ := eq15 X0 (M.op X2 X2)
       have i₂ := eq386 (σ X0) X1 X2
       grind)
    | exact superpose eq386 eq15
    | exact resolve eq15 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq984 : ∀ X0 X1 X2 : G, (σ (k X0 (M.op X1 X1))) = (σ (k X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq979 X0 X1 X2
       have i₂ := eq15 X0 (M.op X1 X1)
       grind)
    | exact superpose eq15 eq979
    | exact resolve eq979 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1266 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq217 X0 X1 X0
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq217 X1 X1 x
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq217 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq217 X1 X1 x
       grind)
    | exact resolve eq14 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1277 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1266 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1266
    | (have j0 := eq1266 (σ X0) (σ X1)
       grind)
    | exact resolve eq1266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1291 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq1266 X0 (τ X1)
       grind)
    | exact superpose eq1266 eq18
    | (have j1 := eq1266 X0 (τ X1)
       grind)
    | exact resolve eq18 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1339 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq61 (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X1 (M.op X4 X4)) X5 X3
       have i₂ := eq61 X1 X0 X2 X4
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1389 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op X0 X1) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq1339 X0 X1 x x X4 X5
       have i₂ := eq99 (M.op X0 X1) x x
       grind)
    | exact superpose eq99 eq1339
    | exact resolve eq1339 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq1624 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1277 X0 X1
       have i₂ := eq1266 X0 X1
       grind)
    | exact superpose eq1266 eq1277
    | (have j0 := eq1277 X0 X1
       have j1 := eq1266 (σ X0) (σ X1)
       grind)
    | exact resolve eq1277 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1801 : ∀ X0 X1 X3 : G, (σ (M.op X0 (M.op X1 X1))) = (σ (k X0 (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq984 X0 x X3
       have i₂ := eq338 X0 X1 x
       grind)
    | exact superpose eq338 eq984
    | exact resolve eq984 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2077 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1801 (M.op X1 X1) X2 x
       have i₂ := eq351 X0 X1 x
       grind)
    | exact superpose eq351 eq1801
    | exact resolve eq1801 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351 eq1801
  have eq2123 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq2077 X0 x X2
       have i₂ := eq73 x (M.op X2 X2)
       grind)
    | exact superpose eq73 eq2077
    | exact resolve eq2077 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq3896 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X4 X4)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 X3)) (M.op X2 X0) X4
       have i₂ := eq1389 X2 X0 X1 X3
       grind)
    | exact superpose eq1389 eq9
    | exact resolve eq9 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389
  have eq4047 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq3896 X0 x X2 X3 x
       have i₂ := eq99 X0 x x
       grind)
    | exact superpose eq99 eq3896
    | exact resolve eq3896 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896
  have eq4133 : ∀ X0 X1 X3 : G, (k X0 (M.op X1 X1)) = (M.op X3 (M.op X0 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq4047 X3 X0 x
       have i₂ := eq338 X0 x X1
       grind)
    | exact superpose eq338 eq4047
    | exact resolve eq4047 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4178 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X3 X3)) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq99 X1 X3 x
       have i₂ := eq4047 X0 X1 x
       grind)
    | (have i₁ := eq99 X0 X1 X0
       have i₂ := eq4047 X0 X0 X3
       grind)
    | exact superpose eq4047 eq99
    | exact resolve eq99 eq4047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq4785 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 X0)) (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4178 X0 X1 x
       have i₂ := eq338 (M.op X0 (M.op X1 X0)) x X2
       grind)
    | exact superpose eq338 eq4178
    | exact resolve eq4178 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338 eq4178
  have eq5210 : ∀ X0 X1 X3 : G, (σ (k X1 (M.op X3 X3))) = (σ (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq984 X1 x X3
       have i₂ := eq4133 X1 x X0
       grind)
    | exact superpose eq4133 eq984
    | exact resolve eq984 eq4133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq8662 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1291 (τ X1) X1
       have i₂ := eq65 X0 (τ X1)
       grind)
    | (have i₁ := eq1291 (τ X1) X1
       have i₂ := eq65 (τ X1) X1
       grind)
    | exact superpose eq65 eq1291
    | exact resolve eq1291 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291
  have eq8707 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 X1) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8662 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq8662
    | (have j0 := eq8662 X0 X1
       grind)
    | exact resolve eq8662 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8662
  have eq8835 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k X1 (τ (σ X1))) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (σ X1)
       have i₂ := eq8707 X0 (σ X1)
       grind)
    | exact superpose eq8707 eq28
    | (have j1 := eq8707 X0 (σ X1)
       grind)
    | exact resolve eq28 eq8707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8707
  have eq8862 : ∀ X0 X1 : G, (k X1 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8835 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8835
    | (have j0 := eq8835 X0 X1
       grind)
    | exact resolve eq8835 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8835
  have eq8924 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8862 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq8862
    | (have j0 := eq8862 X0 X1
       grind)
    | exact resolve eq8862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8862
  have eq8946 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8924 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8924
    | (have j0 := eq8924 X0 X1
       grind)
    | exact resolve eq8924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8924
  have eq9216 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8946 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8946
  have eq9342 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (τ (σ (M.op X0 X0))) (M.op X1 X1))) ∨ (M.op X2 X2) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9216 X2 (σ (M.op X0 X0))
       have i₂ := eq279 (σ (M.op X0 X0)) X1 X0
       grind)
    | exact superpose eq279 eq9216
    | (have j0 := eq9216 X2 (σ (M.op X0 X0))
       grind)
    | exact resolve eq9216 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq9348 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) ≠ (τ (M.op (σ (τ (M.op X0 X0))) (M.op X1 X1))) ∨ (M.op X2 X2) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9216 X2 (τ (M.op X0 X0))
       have i₂ := eq258 (τ (M.op X0 X0)) X1 X0
       grind)
    | exact superpose eq258 eq9216
    | (have j0 := eq9216 X2 (τ (M.op X0 X0))
       grind)
    | exact resolve eq9216 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq9216
  have eq9371 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) ≠ (τ (M.op (M.op X0 X0) (M.op X1 X1))) ∨ (M.op X2 X2) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9348 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq9348
    | (have j0 := eq9348 X0 X1 X2
       grind)
    | exact resolve eq9348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9348
  have eq9377 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X1 X1))) ∨ (M.op X2 X2) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9342 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq9342
    | (have j0 := eq9342 X0 X1 X2
       grind)
    | exact resolve eq9342 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9342
  have eq9383 : ∀ X0 X1 X2 : G, (τ (M.op X1 X1)) ≠ (τ (M.op X0 X0)) ∨ (M.op X2 X2) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9371 X0 X1 X2
       have i₂ := eq73 X0 (M.op X1 X1)
       grind)
    | exact superpose eq73 eq9371
    | (have j0 := eq9371 X0 X1 X2
       grind)
    | exact resolve eq9371 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9371
  have eq9389 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op X2 X2) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9377 X0 X1 X2
       have i₂ := eq73 X0 (M.op X1 X1)
       grind)
    | exact superpose eq73 eq9377
    | (have j0 := eq9377 X0 X1 X2
       grind)
    | exact resolve eq9377 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9377
  have eq9391 : ∀ X0 X2 : G, (M.op X2 X2) = (τ (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq9383 X0 x X2
       grind)
    | (have r₁ := eq9383 X2 X0 X2
       have r₂ := eq861 X0 X2
       grind)
    | (have r₁ := eq9383 X0 X2 X2
       have r₂ := eq861 X0 X2
       grind)
    | exact resolve eq9383 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq9383
  have eq9393 : ∀ X0 X2 : G, (M.op X2 X2) = (σ (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq9389 X0 x X2
       grind)
    | (have r₁ := eq9389 X2 X0 X2
       have r₂ := eq2123 X0 X2
       grind)
    | (have r₁ := eq9389 X0 X2 X2
       have r₂ := eq2123 X0 X2
       grind)
    | exact resolve eq9389 eq2123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123 eq9389
  have eq9412 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9391 x X1
       have i₂ := eq9391 X0 x
       grind)
    | exact superpose eq9391 eq9391
    | exact resolve eq9391 eq9391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9529 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 X1)) (τ (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4785 X1 X2 x
       have i₂ := eq9391 X0 x
       grind)
    | exact superpose eq9391 eq4785
    | exact resolve eq4785 eq9391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4785
  have eq9561 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X1 X1) (M.op X2 X2))) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq334 (M.op X1 X1) X2 X1
       have i₂ := eq9391 X0 (M.op X1 X1)
       grind)
    | exact superpose eq9391 eq334
    | exact resolve eq334 eq9391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq9651 : ∀ X0 X2 : G, (τ (M.op X2 X2)) = (τ (τ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq9561 X0 x X2
       have i₂ := eq73 x (M.op X2 X2)
       grind)
    | exact superpose eq73 eq9561
    | exact resolve eq9561 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9561
  have eq9825 : ∀ X0 X1 X3 : G, (k X1 (σ (M.op X0 X0))) = (M.op X3 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq4133 X1 x X3
       have i₂ := eq9393 X0 x
       grind)
    | exact superpose eq9393 eq4133
    | exact resolve eq4133 eq9393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4133 eq9393
  have eq15767 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1624 x y
       grind)
    | exact superpose eq1624 eq16
    | (have j1 := eq1624 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1624 x y
       grind)
    | exact resolve eq16 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624
  have eq15925 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15767
  have eq22863 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15925
       grind)
    | exact superpose eq15925 eq16
    | exact resolve eq16 eq15925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22866 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq15925
       grind)
    | exact superpose eq15925 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq15925
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15925
       grind)
    | exact resolve eq13 eq15925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22890 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22866
  have eq22894 : (σ x) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22890
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq22890
    | exact resolve eq22890 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22890
  have eq22895 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1266 eq22894
    | (have j1 := eq1266 (σ y) (σ y)
       grind)
    | exact resolve eq22894 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22894
  have eq22896 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22895
       have r₂ := eq22863
       grind)
    | exact resolve eq22895 eq22863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22863 eq22895
  have eq92006 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22896
       have i₂ := eq65 X0 (σ y)
       grind)
    | (have i₁ := eq22896
       have i₂ := eq65 (σ y) X0
       grind)
    | exact superpose eq65 eq22896
    | exact resolve eq22896 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92164 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9391 (σ y) X0
       have i₂ := eq22896
       grind)
    | exact superpose eq22896 eq9391
    | exact resolve eq9391 eq22896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92171 : ∀ X0 : G, (M.op X0 X0) = (τ (τ (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9412 (σ y) X0
       have i₂ := eq22896
       grind)
    | exact superpose eq22896 eq9412
    | exact resolve eq9412 eq22896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9412
  have eq92490 : ∀ X0 : G, (M.op X0 X0) = (τ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq92171 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq92171
    | exact resolve eq92171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92171
  have eq92492 : ∀ X0 : G, y = (M.op X0 X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq92164 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq92164
    | exact resolve eq92164 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92164
  have eq92520 : x = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq92492 eq22896
    | exact resolve eq22896 eq92492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22896 eq92492
  have eq93263 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92520 eq15925
    | exact resolve eq15925 eq92520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15925 eq92520
  have eq93452 : ∀ X0 : G, y = (τ (M.op X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq92006 X0
       grind)
    | exact superpose eq92006 eq10
    | exact resolve eq10 eq92006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92006
  have eq94965 : ∀ X0 : G, y = (τ (τ (M.op X0 X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq93452 x
       have i₂ := eq9391 X0 x
       grind)
    | exact superpose eq9391 eq93452
    | exact resolve eq93452 eq9391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95240 : x = (M.op x y) ∨ y = (τ y) := by
    first
    | exact superpose eq93452 eq94965
    | exact resolve eq94965 eq93452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94965
  have eq96122 : ∀ X0 X1 : G, (k (M.op X0 (τ y)) (τ (M.op X1 X1))) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq9529 X1 X0 X0
       have i₂ := eq92490 X0
       grind)
    | exact superpose eq92490 eq9529
    | exact resolve eq9529 eq92490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9529 eq92490
  have eq96503 : ∀ X0 : G, (k (M.op X0 (τ y)) y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq93452 eq96122
    | exact resolve eq96122 eq93452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93452 eq96122
  have eq97023 : ∀ X0 : G, (k (M.op X0 y) y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq95240 eq96503
    | exact resolve eq96503 eq95240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96503
  have eq103732 : (σ x) = (k (σ x) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq97023 (σ x)
       have i₂ := eq93263
       grind)
    | exact superpose eq93263 eq97023
    | exact resolve eq97023 eq93263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93263 eq97023
  have eq103803 : (σ x) = (k (σ x) y) ∨ x = (M.op x y) := by grind
  clear eq103732
  have eq108072 : (τ (σ x)) = (k x (τ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq103803
       grind)
    | exact superpose eq103803 eq28
    | exact resolve eq28 eq103803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq103803
  have eq108082 : x = (k x (τ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108072
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq108072
    | exact resolve eq108072 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108072
  have eq108086 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq95240 eq108082
    | exact resolve eq108082 eq95240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95240 eq108082
  have eq108097 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1266 x y
       have i₂ := eq108086
       grind)
    | exact superpose eq108086 eq1266
    | (have j0 := eq1266 x y
       grind)
    | exact resolve eq1266 eq108086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266 eq108086
  have eq108098 : x = (M.op x y) := by grind
  clear eq108097
  have eq108106 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq108098
       grind)
    | exact superpose eq108098 eq16
    | exact resolve eq16 eq108098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108107 : ∀ X0 : G, y = (M.op (M.op x (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq108098
       grind)
    | exact superpose eq108098 eq9
    | exact resolve eq9 eq108098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108108 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq108098
       grind)
    | exact superpose eq108098 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq108098
       grind)
    | exact resolve eq13 eq108098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108125 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq4047 y x X0
       have i₂ := eq108098
       grind)
    | exact superpose eq108098 eq4047
    | exact resolve eq4047 eq108098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4047
  have eq108155 : y = (M.op y y) ∨ x = (k x y) := by grind
  clear eq108108
  have eq108690 : y = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq108107 x
       have i₂ := eq108125 x
       grind)
    | exact superpose eq108125 eq108107
    | exact resolve eq108107 eq108125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108107 eq108125
  have eq114397 : ∀ X0 : G, x = (k x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 y X0
       have i₂ := eq108155
       grind)
    | exact superpose eq108155 eq73
    | exact resolve eq73 eq108155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq108155
  have eq117768 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1277 x y
       have i₂ := eq114397 X0
       grind)
    | exact superpose eq114397 eq1277
    | (have j0 := eq1277 x y
       have j1 := eq114397 X0
       grind)
    | exact resolve eq1277 eq114397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277 eq114397
  have eq117771 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq117768 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117768
  have eq117773 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq117771 X0
       grind)
    | (have r₁ := eq117771 X0
       have r₂ := eq108106
       grind)
    | exact resolve eq117771 eq108106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117771
  have eq117788 : y = (M.op x x) := by
    first
    | (have i₁ := eq108690
       have i₂ := eq117773 x
       grind)
    | exact superpose eq117773 eq108690
    | exact resolve eq108690 eq117773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108690 eq117773
  have eq118499 : ∀ X0 : G, y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq117788
       have i₂ := eq65 X0 x
       grind)
    | (have i₁ := eq117788
       have i₂ := eq65 x X0
       grind)
    | exact superpose eq65 eq117788
    | exact resolve eq117788 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq118504 : ∀ X0 : G, y = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq117788
       have i₂ := eq9391 X0 x
       grind)
    | exact superpose eq9391 eq117788
    | exact resolve eq117788 eq9391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9391
  have eq118858 : ∀ X0 : G, (σ (M.op x y)) = (σ (k x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5210 x x X0
       have i₂ := eq117788
       grind)
    | exact superpose eq117788 eq5210
    | exact resolve eq5210 eq117788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5210 eq117788
  have eq118891 : ∀ X0 : G, (σ x) = (σ (k x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq118858 X0
       have i₂ := eq108098
       grind)
    | exact superpose eq108098 eq118858
    | exact resolve eq118858 eq108098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108098 eq118858
  have eq119925 : ∀ X2 : G, (τ (M.op X2 X2)) = (τ y) := by
    intro X2
    first
    | (have i₁ := eq9651 x X2
       have i₂ := eq118504 x
       grind)
    | exact superpose eq118504 eq9651
    | exact resolve eq9651 eq118504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9651
  have eq120113 : y = (τ y) := by
    first
    | (have i₁ := eq119925 x
       have i₂ := eq118504 x
       grind)
    | exact superpose eq118504 eq119925
    | exact resolve eq119925 eq118504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118504 eq119925
  have eq120129 : y = (σ y) := by
    first
    | (have i₁ := eq11 y
       have i₂ := eq120113
       grind)
    | exact superpose eq120113 eq11
    | exact resolve eq11 eq120113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120113
  have eq120154 : (σ x) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq108106
       have i₂ := eq120129
       grind)
    | exact superpose eq120129 eq108106
    | exact resolve eq108106 eq120129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108106 eq120129
  have eq120222 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq120154
       have i₂ := eq118499 X0
       grind)
    | exact superpose eq118499 eq120154
    | exact resolve eq120154 eq118499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118499 eq120154
  have eq120305 : ∀ X0 : G, (σ x) ≠ (k (σ x) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq120222 (σ x)
       have i₂ := eq9825 X0 (σ x) (σ x)
       grind)
    | exact superpose eq9825 eq120222
    | exact resolve eq120222 eq9825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9825 eq120222
  have eq120315 : ∀ X0 : G, (σ x) ≠ (σ (k x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq120305 X0
       have i₂ := eq15 x (M.op X0 X0)
       grind)
    | exact superpose eq15 eq120305
    | exact resolve eq120305 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120305
  have eq120334 : False := by grind
  exact eq120334

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_x_pxx_pyx_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq59 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
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
  have eq60 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
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
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq38
  have eq326 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq62
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq62 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq62 eq14
    | exact resolve eq14 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq326 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq326 X1 X0
       grind)
    | exact superpose eq326 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq326 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq326 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq326 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq326 X0 X1
       grind)
    | exact superpose eq326 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq326 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq326 X1 X1
       grind)
    | exact resolve eq12 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq366 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq382 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq340 X0 (M.op X0 X0)
       grind)
    | exact superpose eq340 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq340 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq382 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq397 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq104 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq104
    | (have j0 := eq104 (σ X0)
       grind)
    | exact resolve eq104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq417 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op X1 X1)
       have i₂ := eq393 X1 (τ X0)
       grind)
    | exact superpose eq393 eq34
    | exact resolve eq34 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq420 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq417 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq417
    | exact resolve eq417 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq430 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq61 X0 X0 X0 X1
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 X1 (M.op X1 X1) X2
       have i₂ := eq62 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq62 eq61
    | exact resolve eq61 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq62
  have eq807 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 (M.op X1 X1)
       have i₂ := eq393 X1 (σ X0)
       grind)
    | exact superpose eq393 eq312
    | exact resolve eq312 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq393
  have eq836 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq807 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq807
    | exact resolve eq807 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq4080 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq420 (σ (M.op X1 X1)) X1
       have i₂ := eq370 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq370 eq420
    | (have j1 := eq370 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq420 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq4123 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq4131 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4080 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4080
  have eq4392 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq340 x X2
       have i₂ := eq4131 x X0
       grind)
    | exact superpose eq4131 eq340
    | exact resolve eq340 eq4131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4131
  have eq6212 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq397 X0
       have i₂ := eq326 X0 (σ X0)
       grind)
    | (have i₁ := eq397 X0
       have i₂ := eq326 (σ X0) X1
       grind)
    | exact superpose eq326 eq397
    | exact resolve eq397 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq6896 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq430 X1 x (M.op X0 (M.op X3 X3)) X5
       have i₂ := eq437 X1 X0 X3 X2 x
       grind)
    | (have i₁ := eq430 (M.op X1 X1) X1 (M.op X1 X0) X3
       have i₂ := eq437 X0 X1 X2 (M.op X1 X1) x
       grind)
    | exact superpose eq437 eq430
    | exact resolve eq430 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq437
  have eq7034 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6896 X0 X1 x X3 x
       have i₂ := eq451 x (M.op X0 X1) x
       grind)
    | exact superpose eq451 eq6896
    | exact resolve eq6896 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq6896
  have eq18746 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X0)) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq7034 (M.op X1 X2) X0 x
       grind)
    | (have i₁ := eq14 X0 X1 (M.op X1 X0)
       have i₂ := eq7034 (M.op X1 X0) (M.op X1 X0) x
       grind)
    | exact superpose eq7034 eq14
    | exact resolve eq14 eq7034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18780 : ∀ X0 : G, y = (M.op (M.op X0 (M.op (M.op x y) X0)) x) := by
    intro X0
    first
    | (have i₁ := eq59 x
       have i₂ := eq7034 sF0 x x
       grind)
    | (have i₁ := eq59 sF0
       have i₂ := eq7034 sF0 sF0 x
       grind)
    | exact superpose eq7034 eq59
    | exact resolve eq59 eq7034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq18788 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq60 x
       have i₂ := eq7034 sF4 x x
       grind)
    | (have i₁ := eq60 sF4
       have i₂ := eq7034 sF4 sF4 x
       grind)
    | exact superpose eq7034 eq60
    | exact resolve eq60 eq7034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq7034
  have eq39889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq39890 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq39889
    | exact resolve eq39889 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39889
  have eq39895 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq39890
       have r₂ := eq27
       grind)
    | exact resolve eq39890 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39890
  have eq39897 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq39895
    | exact resolve eq39895 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39895
  have eq40031 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq39897 eq18746
    | exact resolve eq18746 eq39897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39897
  have eq40035 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18788 eq40031
    | exact resolve eq40031 eq18788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18788 eq40031
  have eq40090 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq40035 eq836
    | exact resolve eq836 eq40035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq40035
  have eq40231 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28 eq40090
    | exact resolve eq40090 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40090
  have eq40239 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq40231 X0
       have j1 := eq349 X0 x X0
       grind)
    | (have r₁ := eq40231 (M.op X0 X0)
       have r₂ := eq349 X0 (k (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq40231 X0
       have r₂ := eq349 x (M.op x y) x
       grind)
    | (have r₁ := eq40231 X0
       have r₂ := eq349 x x x
       grind)
    | exact resolve eq40231 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq40231
  have eq41351 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op (M.op x y) X0)) x) ∨ (σ x) = (σ y) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18746 X0 x x
       have i₂ := eq40239 X1
       grind)
    | (have i₁ := eq18746 X0 X1 x
       have i₂ := eq40239 (M.op X1 x)
       grind)
    | exact superpose eq40239 eq18746
    | (have j1 := eq40239 X1
       grind)
    | exact resolve eq18746 eq40239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18746 eq40239
  have eq41354 : ∀ X1 : G, (k X1 x) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq18780 eq41351
    | (have j0 := eq41351 x X1
       grind)
    | exact resolve eq41351 eq18780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18780 eq41351
  have eq41452 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4123 X0 x
       have i₂ := eq41354 x
       grind)
    | exact superpose eq41354 eq4123
    | (have j0 := eq4123 X0 x
       grind)
    | (have r₁ := eq4123 X0 x
       have r₂ := eq41354 x
       grind)
    | exact resolve eq4123 eq41354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4123
  have eq41453 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq6212 X0 x
       have i₂ := eq41354 x
       grind)
    | exact superpose eq41354 eq6212
    | (have j0 := eq6212 X0 x
       grind)
    | exact resolve eq6212 eq41354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6212 eq41354
  have eq41480 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq41453 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41453
  have eq41481 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq41452 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41452
  have eq41505 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq41480 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq41480
    | (have j0 := eq41480 X0
       grind)
    | exact resolve eq41480 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41480
  have eq42084 : ∀ X1 : G, (M.op x X1) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq340 x X1
       have i₂ := eq41481 x
       grind)
    | exact superpose eq41481 eq340
    | exact resolve eq340 eq41481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq42706 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq41481 x
       have i₂ := eq41505 x
       grind)
    | exact superpose eq41505 eq41481
    | exact resolve eq41481 eq41505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41481 eq41505
  have eq42810 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by grind
  clear eq42706
  have eq42895 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq42810 eq29
    | exact resolve eq29 eq42810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42810
  have eq42963 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq28 eq42895
    | exact resolve eq42895 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42895
  have eq42964 : x = (σ x) ∨ x = y := by grind
  clear eq42963
  have eq42966 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | exact superpose eq42964 eq26
    | exact resolve eq26 eq42964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42964
  have eq44338 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq42084 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42084
    | (have j0 := eq42084 y
       grind)
    | exact resolve eq42084 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44896 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq44338 eq29
    | exact resolve eq29 eq44338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44338
  have eq44970 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq44896
    | exact resolve eq44896 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44896
  have eq44971 : y = (M.op x y) ∨ x = y := by grind
  clear eq44970
  have eq44973 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq44971 eq20
    | exact resolve eq20 eq44971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44971
  have eq45139 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq44973
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44973
    | exact resolve eq44973 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44973
  have eq45189 : (M.op (σ x) (σ y)) = (M.op x (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq45139 eq42966
    | exact resolve eq42966 eq45139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42966 eq45139
  have eq45196 : (M.op (σ x) (σ y)) = (M.op x (σ (M.op x y))) ∨ x = y := by grind
  clear eq45189
  have eq45838 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq45196 eq42084
    | exact resolve eq42084 eq45196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42084 eq45196
  have eq45855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq45838
  have eq45862 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq45855
       have r₂ := eq27
       grind)
    | exact resolve eq45855 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45855
  have eq45866 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq45862 eq29
    | exact resolve eq29 eq45862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq45862
  have eq45943 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq45866
    | exact resolve eq45866 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq45866
  have eq45944 : x = y := by grind
  clear eq45943
  have eq45946 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq45944
       grind)
    | exact superpose eq45944 eq18
    | exact resolve eq18 eq45944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq45947 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq45944
       grind)
    | exact superpose eq45944 eq24
    | exact resolve eq24 eq45944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq45944
  have eq46091 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq45947
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45947
    | exact resolve eq45947 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45947
  have eq46097 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq46091 eq26
    | exact resolve eq26 eq46091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq46091
  have eq46185 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq45946
       have i₂ := eq326 X0 x
       grind)
    | (have i₁ := eq45946
       have i₂ := eq326 x X0
       grind)
    | exact superpose eq326 eq45946
    | exact resolve eq45946 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq45946
  have eq47468 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46097 eq46185
    | exact resolve eq46185 eq46097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46097
  have eq47704 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4392 X0 (σ (M.op X0 X0))
       have i₂ := eq46185 (σ (M.op X0 X0))
       grind)
    | exact superpose eq46185 eq4392
    | exact resolve eq4392 eq46185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4392
  have eq47752 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq47704 x
       have i₂ := eq46185 x
       grind)
    | exact superpose eq46185 eq47704
    | exact resolve eq47704 eq46185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46185 eq47704
  have eq47967 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq47752
    | exact resolve eq47752 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq47752
  have eq48080 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq47468 eq27
    | exact resolve eq27 eq47468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq47468
  have eq48176 : False := by grind
  exact eq48176

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_y_pxy_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X1 (M.op X1 X1) X0
       have i₂ := eq9 X1 X1 X1
       grind)
    | exact superpose eq9 eq106
    | exact resolve eq106 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq127 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq113
    | exact resolve eq113 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq113
  have eq3459 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq4354 : ∀ X0 X1 X2 X3 : G, (σ X2) = (M.op (M.op (σ X0) (M.op X1 X1)) (M.op (M.op (σ X0) (σ X0)) (M.op X3 X3))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (σ X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq103 (σ X0) (σ X2) X3 X1
       have i₂ := eq3459 X0 X2
       grind)
    | (have i₁ := eq103 (σ X0) (σ X0) X2 X3
       have i₂ := eq3459 X0 X1
       grind)
    | exact superpose eq3459 eq103
    | (have j1 := eq3459 X0 X2
       grind)
    | exact resolve eq103 eq3459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3459
  have eq4361 : ∀ X0 X2 : G, (σ X0) = (σ X2) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (σ X2) := by
    intro X0 X2
    first
    | (have i₁ := eq4354 X0 x X2 x
       have i₂ := eq103 (σ X0) (σ X0) x x
       grind)
    | exact superpose eq103 eq4354
    | (have j0 := eq4354 X0 x X2 x
       grind)
    | exact resolve eq4354 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq4354
  have eq4362 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (σ X2) := by
    intro X0 X2
    first
    | (have j0 := eq4361 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4361
  have eq17802 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4362 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq4362
    | (have j0 := eq4362 (τ X0) (τ X1)
       grind)
    | exact resolve eq4362 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq17840 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17802 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq17802
    | (have j0 := eq17802 X0 X1
       grind)
    | exact resolve eq17802 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17802
  have eq17866 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17840 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17840
    | (have j0 := eq17840 X0 X1
       grind)
    | exact resolve eq17840 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17840
  have eq17873 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17866 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq17866
    | (have j0 := eq17866 X0 X1
       grind)
    | exact resolve eq17866 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17866
  have eq17875 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17873 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq17873
    | (have j0 := eq17873 X0 X1
       grind)
    | exact resolve eq17873 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17873
  have eq17877 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17875 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17875
    | (have j0 := eq17875 X0 X1
       grind)
    | exact resolve eq17875 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17875
  have eq17901 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4362 X0 X1
       have i₂ := eq17877 X0 X1
       grind)
    | exact superpose eq17877 eq4362
    | (have j0 := eq4362 X0 X1
       have j1 := eq17877 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq4362 eq17877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4362 eq17877
  have eq491910 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq17901 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17901
  have eq492165 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq491910 x y
       grind)
    | exact superpose eq491910 eq16
    | (have j1 := eq491910 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq491910 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq491910 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq491910 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq491910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491910
  have eq492290 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq492165
  have eq492394 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq492290
       grind)
    | exact superpose eq492290 eq10
    | exact resolve eq10 eq492290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492290
  have eq492548 : x = y ∨ x = y := by
    first
    | (have i₁ := eq492394
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq492394
    | exact resolve eq492394 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492394
  have eq492549 : x = y := by grind
  clear eq492548
  have eq492550 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq492549
       grind)
    | exact superpose eq492549 eq16
    | exact resolve eq16 eq492549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492549
  have eq492551 : False := by grind
  exact eq492551

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_y_pxy_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
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
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x (M.op x x)
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq535 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq56 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq535 (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq535
    | exact resolve eq535 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq610 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq55 X0 X0 X0 X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 X1)) = (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq620 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq633 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X1 (M.op X1 X1) X2
       have i₂ := eq56 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq5130 : ∀ X0 X1 X3 : G, (M.op x (M.op X1 X1)) = (M.op y (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq610 y x (M.op x (M.op X1 X1)) X3
       have i₂ := eq619 X1 X0 x
       grind)
    | exact superpose eq619 eq610
    | exact resolve eq610 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq5140 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq5130 x X1 x
       have i₂ := eq633 x sF0 x
       grind)
    | exact superpose eq633 eq5130
    | exact resolve eq5130 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5130
  have eq5183 : ∀ X1 : G, x = (M.op (M.op y (M.op x y)) (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq633 X1 x x
       have i₂ := eq5140 x
       grind)
    | exact superpose eq5140 eq633
    | exact resolve eq633 eq5140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5140
  have eq5321 : ∀ X0 X1 X3 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | exact superpose eq620 eq610
    | exact resolve eq610 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq5331 : ∀ X1 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq5321 x X1 x
       have i₂ := eq633 x sF4 x
       grind)
    | exact superpose eq633 eq5321
    | exact resolve eq5321 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5321
  have eq5374 : ∀ X1 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq5331 eq633
    | exact resolve eq633 eq5331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5331
  have eq6459 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq610 X1 x (M.op X0 (M.op X3 X3)) X5
       have i₂ := eq617 X1 X0 X3 X2 x
       grind)
    | (have i₁ := eq610 (M.op X1 X1) X1 (M.op X1 X0) X3
       have i₂ := eq617 X0 X1 X2 (M.op X1 X1) x
       grind)
    | exact superpose eq617 eq610
    | exact resolve eq610 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq617
  have eq6623 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6459 X0 X1 x X3 x
       have i₂ := eq633 x (M.op X0 X1) x
       grind)
    | exact superpose eq633 eq6459
    | exact resolve eq6459 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq6459
  have eq7056 : ∀ X1 : G, x = (M.op X1 (M.op (M.op y (M.op x y)) X1)) := by
    intro X1
    first
    | exact superpose eq5183 eq6623
    | exact resolve eq6623 eq5183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5183
  have eq7057 : ∀ X1 : G, (σ x) = (M.op X1 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1)) := by
    intro X1
    first
    | exact superpose eq5374 eq6623
    | exact resolve eq6623 eq5374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6623
  have eq7828 : x = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op y (M.op x y))) (σ x)) := by
    first
    | exact superpose eq7057 eq7056
    | exact resolve eq7056 eq7057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7056 eq7057
  have eq16223 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq82 eq11
    | (have j0 := eq11 (σ x) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq11 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq16224 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16223
    | exact resolve eq16223 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16223
  have eq16229 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq16224
       have r₂ := eq28
       grind)
    | exact resolve eq16224 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16224
  have eq16235 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16229 eq68
    | exact resolve eq68 eq16229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16229
  have eq16347 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq16235
    | exact resolve eq16235 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16235
  have eq16348 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16347
  have eq16384 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq535 x X0
       have i₂ := eq16348
       grind)
    | exact superpose eq16348 eq535
    | exact resolve eq535 eq16348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq16348
  have eq17105 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16384 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16384
    | (have j0 := eq16384 y
       grind)
    | exact resolve eq16384 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16384
  have eq17351 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17105 eq30
    | exact resolve eq30 eq17105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17105
  have eq17399 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq17351
    | exact resolve eq17351 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17351
  have eq17400 : y = (M.op x y) ∨ x = y := by grind
  clear eq17399
  have eq17408 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq17400 eq21
    | exact resolve eq21 eq17400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17481 : x = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op y y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq17400 eq7828
    | exact resolve eq7828 eq17400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7828 eq17400
  have eq17483 : x = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq5374 eq17481
    | exact resolve eq17481 eq5374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5374 eq17481
  have eq17544 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17408
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17408
    | exact resolve eq17408 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17408
  have eq17697 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq17544 eq27
    | exact resolve eq27 eq17544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17544
  have eq17778 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq17483 eq580
    | exact resolve eq580 eq17483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq17483
  have eq17891 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17778 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17778
    | (have j0 := eq17778 X0
       grind)
    | exact resolve eq17778 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17778
  have eq18936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq17891 eq17697
    | exact resolve eq17697 eq17891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17697 eq17891
  have eq19075 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq18936
  have eq19113 : x = y := by
    first
    | (have r₁ := eq19075
       have r₂ := eq28
       grind)
    | exact resolve eq19075 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19075
  have eq19123 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq19113
       grind)
    | exact superpose eq19113 eq19
    | exact resolve eq19 eq19113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq19124 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq19113
       grind)
    | exact superpose eq19113 eq25
    | exact resolve eq25 eq19113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq19113
  have eq19244 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq19124
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19124
    | exact resolve eq19124 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq19124
  have eq19462 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19244 eq27
    | exact resolve eq27 eq19244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19244
  have eq20073 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19462 eq68
    | exact resolve eq68 eq19462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq19462
  have eq20204 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq20073
       have i₂ := eq19123
       grind)
    | exact superpose eq19123 eq20073
    | exact resolve eq20073 eq19123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19123 eq20073
  have eq20222 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20204 eq15
    | exact resolve eq15 eq20204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20204
  have eq20265 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq20222
    | exact resolve eq20222 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq20222
  have eq20274 : False := by grind
  exact eq20274

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyx_pxy_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq375 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (σ (M.op X0 X0))) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq56 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq587 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq542 (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq542
    | exact resolve eq542 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq731 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | exact resolve eq69 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq69
  have eq755 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq731 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq731
    | exact resolve eq731 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq782 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq755 X0 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq755
    | (have j0 := eq755 X0 X1
       grind)
    | exact resolve eq755 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq755
  have eq11205 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ (M.op (τ X0) (τ X0))) (σ (M.op X2 X2))) X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq375 X2 X0 (σ X1)
       have i₂ := eq782 X0 X1
       grind)
    | exact superpose eq782 eq375
    | (have j1 := eq782 X0 X1
       grind)
    | exact resolve eq375 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq782
  have eq11297 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (M.op X2 X2)) X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11205 X0 X1 X2
       have i₂ := eq587 (τ X0) (σ (M.op X2 X2))
       grind)
    | exact superpose eq587 eq11205
    | (have j0 := eq11205 X0 X1 X2
       grind)
    | exact resolve eq11205 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11205
  have eq11365 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11297 X0 X1 x
       have i₂ := eq587 x X0
       grind)
    | exact superpose eq587 eq11297
    | (have j0 := eq11297 X0 X1 x
       grind)
    | exact resolve eq11297 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq11297
  have eq11366 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11365 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11365
  have eq27816 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11366 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11366
    | exact resolve eq11366 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11366
  have eq28203 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq27816 x y
       grind)
    | exact superpose eq27816 eq49
    | (have j1 := eq27816 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq49 eq27816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq28401 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq28203
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28203
    | exact resolve eq28203 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28203
  have eq28468 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq28401
    | exact resolve eq28401 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28401
  have eq28503 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28468 eq27816
    | (have j0 := eq27816 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq27816 eq28468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27816 eq28468
  have eq28509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq28503
    | exact resolve eq28503 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28503
  have eq28522 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq28509
       have r₂ := eq28
       grind)
    | exact resolve eq28509 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28509
  have eq28528 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq28522 eq30
    | exact resolve eq30 eq28522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq28522
  have eq28668 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq28528
    | exact resolve eq28528 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28528
  have eq28669 : x = y := by grind
  clear eq28668
  have eq28689 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq28669
       grind)
    | exact superpose eq28669 eq19
    | exact resolve eq19 eq28669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq28690 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq28669
       grind)
    | exact superpose eq28669 eq25
    | exact resolve eq25 eq28669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28669
  have eq28828 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq28690
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28690
    | exact resolve eq28690 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq28690
  have eq28851 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28828 eq27
    | exact resolve eq27 eq28828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28828
  have eq29298 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq28851 eq68
    | exact resolve eq68 eq28851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq28851
  have eq29477 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq29298
       have i₂ := eq28689
       grind)
    | exact superpose eq28689 eq29298
    | exact resolve eq29298 eq28689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28689 eq29298
  have eq29503 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29477 eq15
    | exact resolve eq15 eq29477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29477
  have eq29577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq29503
    | exact resolve eq29503 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq29503
  have eq29598 : False := by grind
  exact eq29598

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxy_pxx_pxy_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq31 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq31
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq66 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (σ (M.op X0 X0))) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq10
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq25 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op (M.op X2 X1) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X1 X2 X3 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq24 X0 X0 X0 X1
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X1 (M.op X4 X4)) X5 X3
       have i₂ := eq24 X1 X0 X2 X4
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X1 (M.op X1 X1) X2
       have i₂ := eq25 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25
  have eq134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq159 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134 x y
       grind)
    | exact superpose eq134 eq16
    | (have j1 := eq134 x y
       grind)
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq211 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1
       have i₂ := eq97 X0 (τ X1)
       grind)
    | (have i₁ := eq32 X1
       have i₂ := eq97 (τ X1) X0
       grind)
    | exact superpose eq97 eq32
    | exact resolve eq32 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq97
  have eq253 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq211 X0 (M.op X1 X1)
       grind)
    | exact superpose eq211 eq9
    | exact resolve eq9 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1089 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq159
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq159
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq159
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq159
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq159 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq1090 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by grind
  clear eq1089
  have eq1628 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110 X0 (σ (M.op X0 X0)) X1 X2
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq110
    | exact resolve eq110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1722 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1628 X0 X1 X2
       have i₂ := eq253 (M.op X0 X0) (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2))
       grind)
    | exact superpose eq253 eq1628
    | exact resolve eq1628 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq2319 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))))) X3) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq66 (M.op X0 X0) X3 X4
       have i₂ := eq116 X0 X0 X1 X0 X2
       grind)
    | (have i₁ := eq66 (M.op X0 (M.op X4 X4)) X1 X2
       have i₂ := eq116 X0 X0 X4 X3 X4
       grind)
    | exact superpose eq116 eq66
    | exact resolve eq66 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq2324 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (σ (M.op X4 X4))) (M.op (M.op X5 X3) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq110 X4 X3 X5 (M.op X0 X0)
       have i₂ := eq116 X0 X0 X1 X0 X2
       grind)
    | (have i₁ := eq110 X0 X1 X2 (M.op X0 (M.op X4 X4))
       have i₂ := eq116 X0 X0 X4 X3 X4
       grind)
    | exact superpose eq116 eq110
    | exact resolve eq110 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq2366 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq112 X1 x (M.op X0 (M.op X3 X3)) X5
       have i₂ := eq116 X1 X0 X3 X2 x
       grind)
    | (have i₁ := eq112 (M.op X1 X1) X1 (M.op X1 X0) X3
       have i₂ := eq116 X0 X1 X2 (M.op X1 X1) x
       grind)
    | exact superpose eq116 eq112
    | exact resolve eq112 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq116
  have eq2457 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2366 X0 X1 x X3 x
       have i₂ := eq125 x (M.op X0 X1) x
       grind)
    | exact superpose eq125 eq2366
    | exact resolve eq2366 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366
  have eq2885 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op X0 X1) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq117 X0 X1 x x X4 X5
       have i₂ := eq125 x (M.op X0 X1) x
       grind)
    | exact superpose eq125 eq117
    | exact resolve eq117 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq125
  have eq4684 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (σ (M.op X4 X4))) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2)))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1722 X4 X3 (M.op X1 X1)
       have i₂ := eq2885 X0 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq2885 eq1722
    | exact resolve eq1722 eq2885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722 eq2885
  have eq16112 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1090
       grind)
    | exact superpose eq1090 eq16
    | exact resolve eq16 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq16113 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16112
       have r₂ := eq211 x (σ x)
       grind)
    | exact resolve eq16112 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16112
  have eq105687 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (σ (M.op (M.op X3 (M.op X4 X4)) (M.op X3 (τ (M.op X0 X0)))))) X1) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2319 X3 X4 (τ X0) X1 X2
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq2319
    | exact resolve eq2319 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq2319
  have eq194708 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X2 X2) (σ (M.op X3 X3))) (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6))))) = X1 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq2324 X4 X5 X6 (M.op X2 X2) X3 X1
       have i₂ := eq2457 X1 X0 X2
       grind)
    | (have i₁ := eq2324 X0 X1 X2 (M.op X0 X1) X4 X1
       have i₂ := eq2457 X0 X1 X3
       grind)
    | exact superpose eq2457 eq2324
    | exact resolve eq2324 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2324 eq2457
  have eq196656 : ∀ X0 X1 X3 X4 X5 X6 : G, (M.op (σ (M.op X3 X3)) (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6))))) = X1 := by
    intro X0 X1 X3 X4 X5 X6
    first
    | (have i₁ := eq194708 X0 X1 x X3 X4 X5 X6
       have i₂ := eq109 x (σ (M.op X3 X3))
       grind)
    | exact superpose eq109 eq194708
    | exact resolve eq194708 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq194708
  have eq197039 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6)))) = X1 := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq196656 X0 X1 x X4 X5 X6
       have i₂ := eq253 x (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6))))
       grind)
    | exact superpose eq253 eq196656
    | exact resolve eq196656 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq196656
  have eq3200483 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op (σ x) (σ (M.op y y))) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2)))) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq197039 (σ x) (σ y) X0 X1 X2
       have i₂ := eq16113
       grind)
    | exact superpose eq16113 eq197039
    | exact resolve eq197039 eq16113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16113 eq197039
  have eq3200506 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3200483 x x x
       have i₂ := eq4684 x x x (σ x) y
       grind)
    | exact superpose eq4684 eq3200483
    | exact resolve eq3200483 eq4684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4684 eq3200483
  have eq3200507 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq3200506
  have eq3200944 : y = (τ (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3200507
       grind)
    | exact superpose eq3200507 eq10
    | exact resolve eq10 eq3200507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3200507
  have eq3201308 : x = y ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq3200944
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3200944
    | exact resolve eq3200944 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3200944
  have eq3223362 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3201308
       grind)
    | exact superpose eq3201308 eq16
    | exact resolve eq16 eq3201308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3201308
  have eq3223363 : (M.op y y) = (M.op y x) := by
    first
    | (have r₁ := eq3223362
       have r₂ := eq211 x (σ x)
       grind)
    | exact resolve eq3223362 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3223362
  have eq3241323 : ∀ X0 X1 X2 : G, y = (M.op (M.op (M.op y x) (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (τ (M.op X2 X2)))))) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105687 X2 y y X0 X1
       have i₂ := eq3223363
       grind)
    | exact superpose eq3223363 eq105687
    | exact resolve eq105687 eq3223363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3223363
  have eq3241355 : x = y := by
    first
    | (have i₁ := eq3241323 x x x
       have i₂ := eq105687 x y x x x
       grind)
    | exact superpose eq105687 eq3241323
    | exact resolve eq3241323 eq105687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105687 eq3241323
  have eq3241409 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3241355
       grind)
    | exact superpose eq3241355 eq16
    | exact resolve eq16 eq3241355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3241355
  have eq3241410 : False := by grind
  exact eq3241410
