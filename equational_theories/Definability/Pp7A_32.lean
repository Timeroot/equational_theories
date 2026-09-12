import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq32 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq45 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq226 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq233 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq226 X0 X1
       have j1 := eq45 X0 X1
       grind)
    | (have r₁ := eq226 X0 X1
       have r₂ := eq45 X0 X1
       grind)
    | (have r₁ := eq226 X1 X1
       have r₂ := eq45 X1 X1
       grind)
    | exact resolve eq226 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq226
  have eq1736 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq233
  have eq1760 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1736 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq2439 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1760 (σ X0) (σ X1)
       grind)
    | exact superpose eq1760 eq15
    | exact resolve eq15 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2452 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2439 X0 X1
       have i₂ := eq1760 X0 X1
       grind)
    | exact superpose eq1760 eq2439
    | exact resolve eq2439 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760 eq2439
  have eq2464 : False := by grind
  exact eq2464

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq192 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq196 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq192 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq192 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq919 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq196
  have eq927 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq919 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq1437 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq927 (σ X0) (σ X1)
       grind)
    | exact superpose eq927 eq15
    | exact resolve eq15 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1450 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1437 X0 X1
       have i₂ := eq927 X0 X1
       grind)
    | exact superpose eq927 eq1437
    | exact resolve eq1437 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927 eq1437
  have eq1462 : False := by grind
  exact eq1462

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pyx_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq41 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq41 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq42 (σ X0)
       grind)
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq44
    | exact resolve eq44 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq44
  have eq183 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq23 X2 X0 X1 x
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq394 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 X0)) X1) X0) = X2 ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 X1 X0 X2
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq183 X0 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq183
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq183 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 X0)) X1) X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq394 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq394 X0 X1 (M.op (M.op (M.op (M.op X1 (M.op X0 X0)) X1) X0) (M.op (M.op (M.op X1 (M.op X0 X0)) X1) X0))
       have r₂ := eq12 X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X1) X0)
       grind)
    | (have r₁ := eq394 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq394 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq431 : ∀ X0 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq429 X0 x X2
       have i₂ := eq183 x X0 X0
       grind)
    | exact superpose eq183 eq429
    | (have j0 := eq429 X0 x X2
       grind)
    | exact resolve eq429 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq429
  have eq451 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq431 (σ X0) (σ X1)
       grind)
    | exact superpose eq431 eq15
    | (have j1 := eq431 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq431 (τ X0) X1
       grind)
    | exact superpose eq431 eq17
    | (have j1 := eq431 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq17 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq431
  have eq5984 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
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
  have eq6036 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5984 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5984
    | (have j0 := eq5984 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq5984 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5984
  have eq77100 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq451 x y
       grind)
    | exact superpose eq451 eq16
    | (have j1 := eq451 x y
       grind)
    | exact resolve eq16 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq79170 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq77100
       have i₂ := eq6036 x y
       grind)
    | exact superpose eq6036 eq77100
    | (have j1 := eq6036 (σ x) (σ y)
       grind)
    | (have r₁ := eq77100
       have r₂ := eq6036 x y
       grind)
    | (have r₁ := eq77100
       have r₂ := eq6036 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq77100
       have r₂ := eq6036 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq77100 eq6036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6036 eq77100
  have eq79171 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq79170
  have eq80800 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq79171
       grind)
    | exact superpose eq79171 eq10
    | exact resolve eq10 eq79171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79171
  have eq80851 : x = y ∨ x = y := by
    first
    | (have i₁ := eq80800
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq80800
    | exact resolve eq80800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80800
  have eq80852 : x = y := by grind
  clear eq80851
  have eq81786 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80852
       grind)
    | exact superpose eq80852 eq16
    | exact resolve eq16 eq80852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80852
  have eq81787 : False := by grind
  exact eq81787

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyx_pxx_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq83
    | exact resolve eq83 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq106 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq106 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq106 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq106 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq111 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq107 y
       grind)
    | exact superpose eq107 eq70
    | exact resolve eq70 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq112 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq107 sF2
       grind)
    | exact superpose eq107 eq49
    | exact resolve eq49 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq113 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq112
       have i₂ := eq107 x
       grind)
    | exact superpose eq107 eq112
    | exact resolve eq112 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq107 sF3
       grind)
    | exact superpose eq107 eq111
    | exact resolve eq111 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq120 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq97
       have i₂ := eq107 sF3
       grind)
    | exact superpose eq107 eq97
    | exact resolve eq97 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq121 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq120
       have i₂ := eq107 y
       grind)
    | exact superpose eq107 eq120
    | exact resolve eq120 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq120
  have eq130 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq432 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op y (M.op x y))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
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
  clear eq1056
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
  clear eq457
  have eq1221 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1091 eq14
    | exact resolve eq14 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
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
  have eq9278 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq432 (M.op X1 (M.op x X1)) sF0 y
       have i₂ := eq53 y X1 x sF0
       grind)
    | exact superpose eq53 eq432
    | exact resolve eq432 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq432
  have eq32120 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op X2 y) X2)) (M.op X3 (M.op X1 X3))) := by
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
  have eq32123 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) = (M.op (M.op X1 (M.op (M.op X2 (σ y)) X2)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq446 eq442
    | exact resolve eq442 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq446
  have eq32605 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) = (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x))) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | exact superpose eq1221 eq32123
    | (have j0 := eq32123 X0 X1 (σ x) X3
       grind)
    | exact resolve eq32123 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221 eq32123
  have eq32608 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq32120 X0 X1 x X3
       have i₂ := eq1109 x
       grind)
    | (have i₁ := eq32120 X0 X1 x X3
       have i₂ := eq1109 X0
       grind)
    | exact superpose eq1109 eq32120
    | (have j0 := eq32120 X0 X1 x X3
       grind)
    | exact resolve eq32120 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109 eq32120
  have eq32934 : ∀ X1 X3 : G, (σ y) = (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x))) (M.op X3 (M.op X1 X3))) := by
    intro X1 X3
    first
    | exact superpose eq1136 eq32605
    | exact resolve eq32605 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136 eq32605
  have eq32935 : ∀ X1 X3 : G, y = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X1 X3
    first
    | exact superpose eq1131 eq32608
    | exact resolve eq32608 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq32608
  have eq124785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq86 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq124792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq124785
    | exact resolve eq124785 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124785
  have eq124803 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq124792
       have r₂ := eq27
       grind)
    | exact resolve eq124792 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124792
  have eq124807 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq124803
    | exact resolve eq124803 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124803
  have eq124956 : (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq124807 eq32934
    | exact resolve eq32934 eq124807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32934 eq124807
  have eq124961 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq124956
       have i₂ := eq1054 sF4 sF2 sF2
       grind)
    | exact superpose eq1054 eq124956
    | exact resolve eq124956 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124956
  have eq125068 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq124961 eq121
    | exact resolve eq121 eq124961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq124961
  have eq125236 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq125068
    | exact resolve eq125068 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125068
  have eq125237 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq125236
  have eq125407 : y = (M.op (M.op x (M.op (M.op x y) x)) (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq32935 x x
       have i₂ := eq125237
       grind)
    | exact superpose eq125237 eq32935
    | exact resolve eq32935 eq125237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32935 eq125237
  have eq125411 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq125407
       have i₂ := eq1054 sF0 x x
       grind)
    | exact superpose eq1054 eq125407
    | exact resolve eq125407 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054 eq125407
  have eq125826 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq114
       have i₂ := eq125411
       grind)
    | exact superpose eq125411 eq114
    | exact resolve eq114 eq125411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq125840 : x = (M.op (M.op y y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1493 y
       have i₂ := eq125411
       grind)
    | exact superpose eq125411 eq1493
    | exact resolve eq1493 eq125411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq125843 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq125411
       grind)
    | exact superpose eq125411 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq125411
       grind)
    | exact resolve eq13 eq125411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125959 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq125843 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125843
  have eq125995 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq125826
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq125826
    | exact resolve eq125826 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125826
  have eq126340 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq125995 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq125995
       grind)
    | exact resolve eq13 eq125995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125995
  have eq126457 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq126340 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126340
  have eq127316 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq125840
       have i₂ := eq125411
       grind)
    | exact superpose eq125411 eq125840
    | exact resolve eq125840 eq125411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125411 eq125840
  have eq127448 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq127316
  have eq127639 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op y (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X1)) (M.op (M.op x y) x)) X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq127448 eq521
    | exact resolve eq521 eq127448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq127705 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op y (M.op X0 (M.op (M.op X2 y) X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X2 X3
    first
    | exact superpose eq9278 eq127639
    | exact resolve eq127639 eq9278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9278 eq127639
  have eq127784 : ∀ X2 X3 : G, (M.op (M.op X3 X2) X3) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X2 X3
    first
    | (have i₁ := eq127705 x X2 X3
       have i₂ := eq452 X2 y x
       grind)
    | exact superpose eq452 eq127705
    | exact resolve eq127705 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq127705
  have eq130573 : (σ (M.op y (M.op x y))) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq125959 sF0
       grind)
    | exact superpose eq125959 eq130
    | exact resolve eq130 eq125959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq125959
  have eq220154 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq127448 eq130573
    | exact resolve eq130573 eq127448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127448 eq130573
  have eq220228 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq220154
  have eq220234 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq220228
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq220228
    | exact resolve eq220228 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220228
  have eq220246 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq220234 eq126457
    | exact resolve eq126457 eq220234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126457 eq220234
  have eq220254 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq220246
  have eq220429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq220254 eq127784
    | exact resolve eq127784 eq220254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127784 eq220254
  have eq220430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq220429
  have eq220432 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq220430
    | exact resolve eq220430 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220430
  have eq220505 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq220432
       have r₂ := eq27
       grind)
    | exact resolve eq220432 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220432
  have eq220514 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq220505 eq29
    | exact resolve eq29 eq220505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq220505
  have eq220753 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq220514
    | exact resolve eq220514 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq220514
  have eq220754 : x = y := by grind
  clear eq220753
  have eq220776 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq220754
       grind)
    | exact superpose eq220754 eq18
    | exact resolve eq18 eq220754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq220777 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq220754
       grind)
    | exact superpose eq220754 eq24
    | exact resolve eq24 eq220754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq220754
  have eq221019 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq220777
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq220777
    | exact resolve eq220777 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq220777
  have eq221052 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq221019 eq26
    | exact resolve eq26 eq221019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq221019
  have eq221832 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq221052 eq113
    | exact resolve eq113 eq221052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq221052
  have eq222171 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq221832
       have i₂ := eq220776
       grind)
    | exact superpose eq220776 eq221832
    | exact resolve eq221832 eq220776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220776 eq221832
  have eq222287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq222171 eq15
    | exact resolve eq15 eq222171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222171
  have eq222373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq222287
    | exact resolve eq222287 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq222287
  have eq222394 : False := by grind
  exact eq222394

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq31 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X2 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq43 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq44 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X2 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq52 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq43 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq110 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq340 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq341 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq340 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq346 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq341 X0 X1
       have j1 := eq110 X0 X1
       grind)
    | (have r₁ := eq341 X0 X1
       have r₂ := eq110 X0 X1
       grind)
    | (have r₁ := eq341 X1 X1
       have r₂ := eq110 X1 X1
       grind)
    | exact resolve eq341 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq341
  have eq361 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq346 (σ X1) (σ X0)
       grind)
    | exact superpose eq346 eq15
    | exact resolve eq15 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq346 X1 X0
       grind)
    | exact superpose eq346 eq361
    | exact resolve eq361 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq361
  have eq368 : False := by grind
  exact eq368

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pxx_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X2 X1
       have j1 := eq14 X2 X1
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X1))) (M.op X1 (M.op X2 X1))) = X2 ∨ (M.op X0 (M.op X1 (M.op X2 X1))) = (k X0 (M.op X1 (M.op X2 X1))) ∨ (M.op X1 (M.op X2 X1)) = (M.op (M.op X1 (M.op X2 X1)) (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X2 X1)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1))
       grind)
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X0 (M.op X2 (M.op X0 X2))
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 (M.op X1 (M.op X2 X1))
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq45 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X1))) (M.op X1 (M.op X2 X1))) = X2 ∨ (M.op X0 (M.op X1 (M.op X2 X1))) = (k X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq29 X0 X1 X2
       have j1 := eq12 X0 (M.op X1 (M.op X2 X1))
       grind)
    | (have r₁ := eq29 X0 X1 X2
       have r₂ := eq12 X0 (M.op X1 (M.op X2 X1))
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq48 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq25 X0 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | (have r₁ := eq25 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq25 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq48 X0 X1 X2
       have j1 := eq39 X1 X2
       grind)
    | (have r₁ := eq48 X1 X0 X2
       have r₂ := eq39 X0 X1
       grind)
    | exact resolve eq48 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq48
  have eq56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23 (σ X0)
       grind)
    | exact superpose eq23 eq15
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq56
    | exact resolve eq56 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq56
  have eq64 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq106 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq158 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X3 X2)) X4) = (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X2 X4 X3 (M.op X1 X2)
       have i₂ := eq19 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X1 X2)
       have i₂ := eq19 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op (M.op X4 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X0))) X3) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X1 X3 (M.op X4 (M.op X2 X4))
       have i₂ := eq19 X2 X0 X1 X4
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 x X0
       have i₂ := eq19 (M.op X2 X0) x X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X0 X2)) = (M.op (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X1))))) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 (M.op X0 X2)) X3 X4
       have i₂ := eq19 X2 X4 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X3)) X0)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X3 X1 X2 x
       have i₂ := eq19 X3 X0 (M.op X1 (M.op X2 X1)) x
       grind)
    | exact superpose eq19 eq20
    | exact resolve eq20 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq53 (σ x) (σ y) X0
       grind)
    | (have i₁ := eq16
       have i₂ := eq53 X0 (σ y) (σ x)
       grind)
    | exact superpose eq53 eq16
    | (have j1 := eq53 (σ x) (σ y) (σ x)
       grind)
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq414 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq372
    | (have j0 := eq372 X0
       grind)
    | exact resolve eq372 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq693 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))))) ∨ (k X1 (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (M.op X0 (M.op x X0)) (M.op x X0)
       have i₂ := eq20 X0 X0 x (M.op x X0)
       grind)
    | exact superpose eq20 eq45
    | exact resolve eq45 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq799 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (k (M.op (σ y) (M.op X1 (M.op X0 X1))) (σ y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq414 (M.op (σ y) (M.op x (M.op X0 x)))
       have i₂ := eq9 X0 (σ y) x
       grind)
    | exact superpose eq9 eq414
    | (have r₁ := eq414 (M.op (σ y) (M.op x (M.op (σ (M.op x y)) x)))
       have r₂ := eq9 (σ (M.op x y)) (σ y) x
       grind)
    | exact resolve eq414 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq988 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq199 (M.op X1 (M.op X0 X1)) X2 X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq199
    | exact resolve eq199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq1107 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) ≠ X0 ∨ (k X1 (M.op (M.op X2 (M.op X0 X2)) (M.op X3 (M.op X1 X3)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq106 X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq106
    | (have r₁ := eq106 X0 (M.op (M.op X1 (M.op (M.op X0 X0) X1)) (M.op X3 (M.op X0 X3)))
       have r₂ := eq20 X0 X1 (M.op X0 X0) X3
       grind)
    | exact resolve eq106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq1187 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op (σ y) (M.op X0 (M.op (σ (M.op x y)) X0))) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0
    first
    | (have j0 := eq799 (σ (M.op x y)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq1906 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 X2)) (M.op (M.op X3 X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X1 (M.op X2 (M.op X1 X2)) (M.op (M.op X2 (M.op X1 X2)) (M.op (M.op X3 X0) X3)) X2
       have i₂ := eq187 (M.op X2 (M.op X1 X2)) X3 X0 (M.op X2 (M.op X1 X2))
       grind)
    | exact superpose eq187 eq20
    | exact resolve eq20 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1993 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X0) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq233 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq233
    | exact resolve eq233 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3396 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 (M.op (M.op X3 X0) X3))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq158 x x (M.op (M.op X3 X0) X3) X2 X1
       have i₂ := eq187 x X3 X0 x
       grind)
    | exact superpose eq187 eq158
    | exact resolve eq158 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq187
  have eq4498 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X5 (M.op X0 X2)) = (M.op (M.op X3 (M.op (M.op X4 (M.op X5 X4)) (M.op (M.op X6 (M.op X0 (M.op X1 (M.op X2 X1)))) X6))) X3) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq188 X6 (M.op X5 (M.op X0 X2)) X5 X3 X4
       have i₂ := eq19 X2 X5 X0 X1
       grind)
    | exact superpose eq19 eq188
    | exact resolve eq188 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq4843 : ∀ X0 X1 X2 X4 X5 : G, (M.op X5 (M.op X0 X2)) = (M.op (M.op X4 (M.op X5 X4)) (M.op X0 (M.op X1 (M.op X2 X1)))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq4498 X0 X1 X2 x X4 X5 x
       have i₂ := eq3396 (M.op X0 (M.op X1 (M.op X2 X1))) x (M.op X4 (M.op X5 X4)) x
       grind)
    | exact superpose eq3396 eq4498
    | exact resolve eq4498 eq3396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3396 eq4498
  have eq5404 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (σ X0))) = (M.op (M.op X3 (M.op X1 (M.op X2 (M.op (σ X0) (σ (M.op X0 X0)))))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq200 X2 (σ X0) (σ X0) X3 X1
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq200
    | exact resolve eq200 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq200
  have eq8452 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (τ (M.op (σ y) (M.op X0 (M.op (σ (M.op x y)) X0)))) y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0
    first
    | (have i₁ := eq64 (M.op (σ y) (M.op X0 (M.op (σ (M.op x y)) X0))) y
       have i₂ := eq1187 X0
       grind)
    | exact superpose eq1187 eq64
    | exact resolve eq64 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq1187
  have eq8471 : ∀ X0 : G, (M.op x y) = (k (τ (M.op (σ y) (M.op X0 (M.op (σ (M.op x y)) X0)))) y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0
    first
    | (have i₁ := eq8452 X0
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq8452
    | exact resolve eq8452 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8452
  have eq55776 : ∀ X0 X1 : G, (M.op x y) = (k (τ (M.op (σ y) (M.op (M.op X0 (M.op (M.op X1 (σ (M.op x y))) X1)) X0))) y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq8471 (M.op X1 (σ (M.op x y)))
       have i₂ := eq19 X1 X0 (M.op X1 (σ (M.op x y))) (σ (M.op x y))
       grind)
    | exact superpose eq19 eq8471
    | exact resolve eq8471 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8471
  have eq157081 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op (M.op X0 X1) X0)) = X0 ∨ (k X1 (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq233 X0 X1 X0 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))
       have i₂ := eq693 X0 X1
       grind)
    | exact superpose eq693 eq233
    | (have j1 := eq693 X0 X1
       grind)
    | exact resolve eq233 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq693
  have eq157814 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X1 (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq157081 X0 X1
       have i₂ := eq1906 X1 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq1906 eq157081
    | (have j0 := eq157081 X0 X1
       grind)
    | exact resolve eq157081 eq1906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906 eq157081
  have eq158476 : ∀ X0 X1 : G, (k X1 (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq157814 X0 X1
       have j1 := eq1107 X0 X1 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq157814 X0 X1
       have r₂ := eq1107 X0 X1 x x
       grind)
    | (have r₁ := eq157814 (M.op X1 X1) X1
       have r₂ := eq1107 (M.op X1 X1) X1 x x
       grind)
    | (have r₁ := eq157814 (M.op X1 X1) X1
       have r₂ := eq1107 (k X1 (M.op (M.op X1 (M.op (M.op X1 X1) X1)) (M.op (M.op (M.op X1 X1) X1) (M.op X1 (M.op (M.op X1 X1) X1))))) X1 x x
       grind)
    | exact resolve eq157814 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107 eq157814
  have eq158950 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op (M.op X0 X1) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq158476 X0 X1
       have i₂ := eq4843 (M.op X0 X1) X1 X0 X1 X0
       grind)
    | (have i₁ := eq158476 X0 X1
       have i₂ := eq4843 (M.op X0 X1) X1 (M.op X1 (M.op X0 X1)) x (M.op X1 (M.op X0 X1))
       grind)
    | exact superpose eq4843 eq158476
    | exact resolve eq158476 eq4843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4843 eq158476
  have eq368477 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq158950 (M.op X1 X0) X1
       have i₂ := eq1993 X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq1993 eq158950
    | exact resolve eq158950 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993 eq158950
  have eq369845 : ∀ X0 X1 : G, (M.op x y) = (k (τ (M.op (σ y) (M.op (M.op X1 (M.op (σ X0) (M.op (σ (M.op x y)) (M.op (σ X0) (σ (M.op X0 X0)))))) X1))) y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq55776 X1 (M.op (σ (M.op x y)) (M.op (σ X0) (σ (M.op X0 X0))))
       have i₂ := eq293 X0 (σ (M.op x y))
       grind)
    | exact superpose eq293 eq55776
    | exact resolve eq55776 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq55776
  have eq369860 : ∀ X0 X1 : G, (M.op x y) = (M.op (τ (M.op (σ y) (M.op (M.op X1 (M.op (σ X0) (M.op (σ (M.op x y)) (M.op (σ X0) (σ (M.op X0 X0)))))) X1))) y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq369845 X0 X1
       have i₂ := eq368477 y (τ (M.op (σ y) (M.op (M.op X1 (M.op (σ X0) (M.op (σ (M.op x y)) (M.op (σ X0) (σ (M.op X0 X0)))))) X1)))
       grind)
    | exact superpose eq368477 eq369845
    | exact resolve eq369845 eq368477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369845
  have eq370168 : ∀ X0 : G, (M.op x y) = (M.op (τ (M.op (σ y) (M.op (σ X0) (M.op (σ (M.op x y)) (σ X0))))) y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0
    first
    | (have i₁ := eq369860 X0 x
       have i₂ := eq5404 X0 (σ X0) (σ (M.op x y)) x
       grind)
    | exact superpose eq5404 eq369860
    | exact resolve eq369860 eq5404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5404 eq369860
  have eq370274 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (τ (M.op (σ y) (M.op (σ X0) (M.op (σ (M.op x y)) (σ X0))))) y) := by
    intro X0
    first
    | (have i₁ := eq370168 X0
       have i₂ := eq368477 y x
       grind)
    | exact superpose eq368477 eq370168
    | (have j0 := eq370168 X0
       grind)
    | exact resolve eq370168 eq368477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370168
  have eq370320 : ∀ X0 : G, (M.op x y) = (M.op (τ (M.op (σ y) (M.op (σ X0) (M.op (σ (M.op x y)) (σ X0))))) y) := by
    intro X0
    first
    | (have j0 := eq370274 X0
       grind)
    | (have r₁ := eq370274 X0
       have r₂ := eq16
       grind)
    | exact resolve eq370274 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370274
  have eq378206 : ∀ X0 X1 : G, (τ (M.op (σ y) (M.op (σ X1) (M.op (σ (M.op x y)) (σ X1))))) = (M.op (M.op X0 (M.op y X0)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq988 y X0 (τ (M.op (σ y) (M.op (σ X1) (M.op (σ (M.op x y)) (σ X1)))))
       have i₂ := eq370320 X1
       grind)
    | exact superpose eq370320 eq988
    | exact resolve eq988 eq370320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370320
  have eq378245 : ∀ X1 : G, x = (τ (M.op (σ y) (M.op (σ X1) (M.op (σ (M.op x y)) (σ X1))))) := by
    intro X1
    first
    | (have i₁ := eq378206 x X1
       have i₂ := eq988 y x x
       grind)
    | exact superpose eq988 eq378206
    | exact resolve eq378206 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988 eq378206
  have eq403034 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ X0) (M.op (σ (M.op x y)) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ y) (M.op (σ X0) (M.op (σ (M.op x y)) (σ X0))))
       have i₂ := eq378245 X0
       grind)
    | exact superpose eq378245 eq11
    | exact resolve eq11 eq378245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403035 : ∀ X0 X1 : G, (σ (k x X1)) = (k (M.op (σ y) (M.op (σ X0) (M.op (σ (M.op x y)) (σ X0)))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (M.op (σ y) (M.op (σ X0) (M.op (σ (M.op x y)) (σ X0)))) X1
       have i₂ := eq378245 X0
       grind)
    | exact superpose eq378245 eq17
    | exact resolve eq17 eq378245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq378245
  have eq403111 : ∀ X0 X1 : G, (σ (k x X1)) = (M.op (M.op (σ y) (M.op (σ X0) (M.op (σ (M.op x y)) (σ X0)))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq403035 X0 X1
       have i₂ := eq368477 (σ X1) (M.op (σ y) (M.op (σ X0) (M.op (σ (M.op x y)) (σ X0))))
       grind)
    | exact superpose eq368477 eq403035
    | exact resolve eq403035 eq368477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403035
  have eq403221 : ∀ X1 : G, (σ (k x X1)) = (M.op (σ x) (σ X1)) := by
    intro X1
    first
    | (have i₁ := eq403111 x X1
       have i₂ := eq403034 x
       grind)
    | exact superpose eq403034 eq403111
    | exact resolve eq403111 eq403034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403034 eq403111
  have eq403269 : ∀ X1 : G, (M.op (σ x) (σ X1)) = (σ (M.op x X1)) := by
    intro X1
    first
    | (have i₁ := eq403221 X1
       have i₂ := eq368477 X1 x
       grind)
    | exact superpose eq368477 eq403221
    | exact resolve eq403221 eq368477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368477 eq403221
  have eq403307 : False := by grind
  exact eq403307

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pyx_Equation2452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 x) x) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq73 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq71
    | (have j0 := eq71 X0
       grind)
    | exact resolve eq71 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq74 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq73 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq80 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq103
    | exact resolve eq103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq17928 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17929 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq17928
    | exact resolve eq17928 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17928
  have eq17940 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17929
       have r₂ := eq29
       grind)
    | exact resolve eq17929 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17929
  have eq17948 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq17940
  have eq17967 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq17948
    | exact resolve eq17948 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17948
  have eq18582 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17967 eq104
    | exact resolve eq104 eq17967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17967
  have eq18594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq18582
  have eq18597 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18594
       have r₂ := eq29
       grind)
    | exact resolve eq18594 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18594
  have eq18602 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18597 eq55
    | exact resolve eq55 eq18597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18604 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18597 eq74
    | exact resolve eq74 eq18597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18597
  have eq18619 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq18602
    | exact resolve eq18602 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18602
  have eq18627 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq18619
  have eq18646 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18627
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq18627
    | exact resolve eq18627 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18627
  have eq18726 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq18646
       grind)
    | exact superpose eq18646 eq80
    | exact resolve eq80 eq18646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18646
  have eq18752 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq18726
    | exact resolve eq18726 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18726
  have eq19123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18752 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq18752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq19123
    | exact resolve eq19123 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19123
  have eq19137 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq19126
       have r₂ := eq29
       grind)
    | exact resolve eq19126 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19126
  have eq19476 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18604 eq104
    | exact resolve eq104 eq18604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq18604
  have eq19491 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq19476
  have eq19510 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq19491
  have eq19529 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19510
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq19510
    | exact resolve eq19510 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19510
  have eq19610 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19529
       grind)
    | exact superpose eq19529 eq80
    | exact resolve eq80 eq19529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19529
  have eq19637 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22 eq19610
    | exact resolve eq19610 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19610
  have eq19884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19637 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq19637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19891 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28 eq19884
    | exact resolve eq19884 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19884
  have eq19902 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq19891
       have r₂ := eq29
       grind)
    | exact resolve eq19891 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19891
  have eq40015 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq19137
  have eq40034 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq40015
    | exact resolve eq40015 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40015
  have eq46567 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq19902
  have eq46586 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28 eq46567
    | exact resolve eq46567 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46567
  have eq46705 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq40034 eq18752
    | exact resolve eq18752 eq40034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18752 eq40034
  have eq46771 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq46705
  have eq46793 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq46771
       have r₂ := eq29
       grind)
    | exact resolve eq46771 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46771
  have eq46803 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46793 eq55
    | exact resolve eq55 eq46793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46793
  have eq46822 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq46803
    | exact resolve eq46803 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46803
  have eq46823 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq46822
  have eq46837 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74 y
       have i₂ := eq46823
       grind)
    | exact superpose eq46823 eq74
    | exact resolve eq74 eq46823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46823
  have eq46868 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq46837
       grind)
    | exact superpose eq46837 eq80
    | exact resolve eq80 eq46837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq46837
  have eq46929 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46868
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq46868
    | exact resolve eq46868 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46868
  have eq46994 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46929 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq46929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47010 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq46994
    | exact resolve eq46994 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46994
  have eq47011 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq47010
  have eq51683 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq47011
  have eq51703 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq51683
    | exact resolve eq51683 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51683
  have eq52709 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51703 eq46929
    | exact resolve eq46929 eq51703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46929 eq51703
  have eq52715 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq52709
  have eq52755 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq52715 eq55
    | exact resolve eq55 eq52715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52715
  have eq52776 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq52755
    | exact resolve eq52755 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq52755
  have eq52777 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq52776
  have eq52779 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq52777 eq29
    | exact resolve eq29 eq52777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq113234 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq46586
       have r₂ := eq52779
       grind)
    | exact resolve eq46586 eq52779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46586
  have eq113235 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq52777 eq113234
    | exact resolve eq113234 eq52777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52777 eq113234
  have eq113270 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq113235 eq19637
    | exact resolve eq19637 eq113235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113235
  have eq113303 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq113270
  have eq113332 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq113303
       have r₂ := eq52779
       grind)
    | exact resolve eq113303 eq52779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113303
  have eq114086 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq113332 eq74
    | exact resolve eq74 eq113332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq113332
  have eq114137 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq114086 eq19637
    | exact resolve eq19637 eq114086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19637 eq114086
  have eq114168 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq114137
  have eq114194 : x = (M.op y y) := by
    first
    | (have r₁ := eq114168
       have r₂ := eq52779
       grind)
    | exact resolve eq114168 eq52779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114168
  have eq114224 : y = (M.op x y) := by
    first
    | (have i₁ := eq55 y
       have i₂ := eq114194
       grind)
    | exact superpose eq114194 eq55
    | exact resolve eq55 eq114194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq114194
  have eq114241 : y = (M.op x y) := by
    first
    | (have i₁ := eq114224
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq114224
    | exact resolve eq114224 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq114224
  have eq114243 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq114241 eq22
    | exact resolve eq22 eq114241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq114241
  have eq114560 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq114243
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq114243
    | exact resolve eq114243 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq114243
  have eq114564 : False := by grind
  exact eq114564

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation2452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq280 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq280 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq283 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq281 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq281 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq281 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq294 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq283 (σ X0)
       grind)
    | exact superpose eq283 eq15
    | exact resolve eq15 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq294 X0
       have i₂ := eq283 X0
       grind)
    | exact superpose eq283 eq294
    | exact resolve eq294 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq294
  have eq359 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq313 X0
       grind)
    | exact superpose eq313 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq313 X0
       grind)
    | exact superpose eq313 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq359 X0 X1
       have j1 := eq361 X0 X1
       grind)
    | (have r₁ := eq359 X0 X1
       have r₂ := eq361 X0 X1
       grind)
    | exact resolve eq359 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq525 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq363 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq363
    | exact resolve eq363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq363 X0 (σ X1)
       grind)
    | exact superpose eq363 eq15
    | (have j1 := eq363 X0 (σ X1)
       grind)
    | exact resolve eq15 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq606 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq525 X0 (τ X1)
       grind)
    | exact superpose eq525 eq17
    | (have j1 := eq525 X0 (τ X1)
       grind)
    | exact resolve eq17 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq525
  have eq974 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq606 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq606
    | exact resolve eq606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq1038 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq974 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq974
    | (have j0 := eq974 X0 X1
       grind)
    | exact resolve eq974 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq2043 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq536 x y
       grind)
    | exact superpose eq536 eq16
    | (have j1 := eq536 x y
       grind)
    | exact resolve eq16 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2084 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq536 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq2272 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2084 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq2084
    | (have j0 := eq2084 (τ X1) (τ X0)
       grind)
    | exact resolve eq2084 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2277 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2084 X0 X1
       have i₂ := eq1038 X1 X0
       grind)
    | exact superpose eq1038 eq2084
    | (have j0 := eq2084 X0 X1
       have j1 := eq1038 (σ X1) (σ X0)
       grind)
    | exact resolve eq2084 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2282 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2272 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2272
    | (have j0 := eq2272 X0 X1
       grind)
    | exact resolve eq2272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272
  have eq2289 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2282 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2282
    | (have j0 := eq2282 X0 X1
       grind)
    | exact resolve eq2282 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282
  have eq2290 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2289 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2289
    | (have j0 := eq2289 X0 X1
       grind)
    | exact resolve eq2289 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2289
  have eq2291 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2290 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2290
    | (have j0 := eq2290 X0 X1
       grind)
    | exact resolve eq2290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq2439 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2043
       have i₂ := eq1038 y x
       grind)
    | exact superpose eq1038 eq2043
    | (have j1 := eq1038 (σ y) (σ x)
       grind)
    | (have r₁ := eq2043
       have r₂ := eq1038 y x
       grind)
    | exact resolve eq2043 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038 eq2043
  have eq2440 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2439
  have eq2446 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2440
       grind)
    | exact superpose eq2440 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2440
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2440
       grind)
    | exact resolve eq13 eq2440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2440
  have eq2448 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq2446
  have eq4377 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2448
       grind)
    | exact superpose eq2448 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2448
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq2448
       grind)
    | exact resolve eq13 eq2448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448
  have eq4379 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq4377
  have eq4380 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4379
       have i₂ := eq313 x
       grind)
    | exact superpose eq313 eq4379
    | exact resolve eq4379 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4379
  have eq4384 : x = (k y x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4380
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4380
    | exact resolve eq4380 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4380
  have eq323737 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2084 x y
       have i₂ := eq4384
       grind)
    | exact superpose eq4384 eq2084
    | (have j0 := eq2084 x y
       grind)
    | (have r₁ := eq2084 x y
       have r₂ := eq4384
       grind)
    | exact resolve eq2084 eq4384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4384
  have eq323848 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x x) := by grind
  clear eq323737
  have eq323854 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq2084 x y
       grind)
    | (have r₁ := eq323848
       have r₂ := eq2084 x y
       grind)
    | exact resolve eq323848 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084 eq323848
  have eq323858 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq323854
       grind)
    | exact superpose eq323854 eq16
    | exact resolve eq16 eq323854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323864 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq323854
       grind)
    | exact superpose eq323854 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq323854
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq323854
       grind)
    | exact resolve eq13 eq323854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323854
  have eq323900 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq323864
  have eq323915 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq2277 x x
       grind)
    | (have r₁ := eq323900
       have r₂ := eq2277 x x
       grind)
    | exact resolve eq323900 eq2277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277 eq323900
  have eq323923 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq323915
       have i₂ := eq313 x
       grind)
    | exact superpose eq313 eq323915
    | exact resolve eq323915 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq323915
  have eq323926 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq323923
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq323923
    | exact resolve eq323923 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323923
  have eq323978 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq323926
       grind)
    | exact superpose eq323926 eq10
    | exact resolve eq10 eq323926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323926
  have eq324187 : x = (k y x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq323978
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq323978
    | exact resolve eq323978 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323978
  have eq324223 : x ≠ x ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2291 y x
       have i₂ := eq324187
       grind)
    | exact superpose eq324187 eq2291
    | (have j0 := eq2291 y x
       grind)
    | (have r₁ := eq2291 y x
       have r₂ := eq324187
       grind)
    | exact resolve eq2291 eq324187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2291 eq324187
  have eq324330 : x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq324223
  have eq324342 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq323858
       have i₂ := eq324330
       grind)
    | exact superpose eq324330 eq323858
    | exact resolve eq323858 eq324330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323858 eq324330
  have eq324386 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq324342
  have eq324387 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq324386
  have eq324434 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq324387
       grind)
    | exact superpose eq324387 eq10
    | exact resolve eq10 eq324387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324387
  have eq324647 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq324434
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq324434
    | exact resolve eq324434 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324434
  have eq324648 : x = (M.op x x) := by grind
  clear eq324647
  have eq324666 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq324648
       grind)
    | exact superpose eq324648 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq324648
       grind)
    | exact resolve eq12 eq324648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324676 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq361 x X0
       have i₂ := eq324648
       grind)
    | exact superpose eq324648 eq361
    | (have j0 := eq361 x X0
       grind)
    | exact resolve eq361 eq324648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq324648
  have eq324858 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq324676 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324676
  have eq324860 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq324666 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324666
  have eq326305 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq324858 (σ X0)
       grind)
    | exact superpose eq324858 eq15
    | exact resolve eq15 eq324858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324858
  have eq326539 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq326305 X0
       have i₂ := eq324860 X0
       grind)
    | exact superpose eq324860 eq326305
    | exact resolve eq326305 eq324860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324860 eq326305
  have eq330656 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq326539 y
       grind)
    | exact superpose eq326539 eq16
    | (have r₁ := eq16
       have r₂ := eq326539 y
       grind)
    | exact resolve eq16 eq326539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326539
  have eq331209 : False := by grind
  exact eq331209
