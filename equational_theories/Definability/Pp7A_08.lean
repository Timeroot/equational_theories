import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_pxy_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq81 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq85
  have eq476 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq512 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq476 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq517 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq512 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq512 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq512 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq512 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq528 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq517 X0 X1
       have j1 := eq81 X0 (σ X1)
       grind)
    | (have r₁ := eq517 X0 X1
       have r₂ := eq81 X0 (σ X1)
       grind)
    | exact resolve eq517 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq517
  have eq536 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq528 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq528
    | (have j0 := eq528 X0 X1
       grind)
    | exact resolve eq528 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq537 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq536 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq543 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq537 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq537
    | exact resolve eq537 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq537 x y
       grind)
    | exact superpose eq537 eq16
    | exact resolve eq16 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq663 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq543 X0 (τ X1)
       grind)
    | exact superpose eq543 eq17
    | exact resolve eq17 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq543
  have eq689 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq663
    | exact resolve eq663 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq702 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq689 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq689
    | exact resolve eq689 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq726 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq554
       have i₂ := eq702 x y
       grind)
    | exact superpose eq702 eq554
    | exact resolve eq554 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq702
  have eq727 : False := by grind
  exact eq727

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxy_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq491 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq527 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq491 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq528 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq527 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq532 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq528 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq528 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq528 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq541 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq532
    | (have j0 := eq532 X0 X1
       grind)
    | exact resolve eq532 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq542 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq541 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq547 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq542 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq542
    | exact resolve eq542 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq542 x y
       grind)
    | exact superpose eq542 eq16
    | exact resolve eq16 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq663 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq547 X0 (τ X1)
       grind)
    | exact superpose eq547 eq17
    | exact resolve eq17 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq547
  have eq689 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq663
    | exact resolve eq663 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq701 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq689 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq689
    | exact resolve eq689 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq725 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq558
       have i₂ := eq701 x y
       grind)
    | exact superpose eq701 eq558
    | exact resolve eq558 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq701
  have eq726 : False := by grind
  exact eq726

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_x_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq24 eq35
  have eq78 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
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
  have eq79 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq96 x y
       grind)
    | exact superpose eq96 eq44
    | (have j1 := eq96 x y
       grind)
    | exact resolve eq44 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122 eq96
    | (have j0 := eq96 (σ x) (σ y)
       grind)
    | exact resolve eq96 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq126
       have r₂ := eq27
       grind)
    | exact resolve eq126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq129
    | exact resolve eq129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq133 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq27
    | exact resolve eq27 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq847 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq79
    | (have r₁ := eq79
       have r₂ := eq131
       grind)
    | exact resolve eq79 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq131
  have eq848 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq847
  have eq851 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq848 eq122
    | exact resolve eq122 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq855 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq851
  have eq860 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq855
       have r₂ := eq133
       grind)
    | exact resolve eq855 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq855
  have eq880 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq860 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq860
       grind)
    | exact resolve eq13 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq891 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq880
  have eq907 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq891
    | exact resolve eq891 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq907 eq122
    | exact resolve eq122 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq907
  have eq963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq960
  have eq967 : x = (M.op x y) := by
    first
    | (have r₁ := eq963
       have r₂ := eq27
       grind)
    | exact resolve eq963 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq969 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq967 eq20
    | exact resolve eq20 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq975 : x ≠ x ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq967 eq78
    | (have r₁ := eq78
       have r₂ := eq967
       grind)
    | exact resolve eq78 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq979 : x = (k x y) ∨ x = (M.op y x) := by grind
  clear eq975
  have eq985 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq969
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq969
    | exact resolve eq969 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq986 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq985 eq26
    | exact resolve eq26 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1673 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq979
       grind)
    | exact superpose eq979 eq44
    | exact resolve eq44 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1680 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq985 eq1673
    | exact resolve eq1673 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq1682 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1680
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1680
    | exact resolve eq1680 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680
  have eq1683 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq985 eq1682
    | exact resolve eq1682 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682
  have eq1716 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1683 eq96
    | (have j0 := eq96 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq96 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683
  have eq1717 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1716
  have eq1719 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq986 eq1717
    | exact resolve eq1717 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq1722 : x = (M.op y x) := by
    first
    | (have r₁ := eq1719
       have r₂ := eq27
       grind)
    | exact resolve eq1719 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq1740 : x ≠ x ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1722
       grind)
    | exact superpose eq1722 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1722
       grind)
    | exact resolve eq13 eq1722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722
  have eq1755 : (M.op x y) = (k x y) := by grind
  clear eq1740
  have eq1756 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1755
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1755
    | exact resolve eq1755 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1755
  have eq1762 : x = (k x y) := by
    first
    | exact superpose eq967 eq1756
    | exact resolve eq1756 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq1756
  have eq1939 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1762
       grind)
    | exact superpose eq1762 eq44
    | exact resolve eq44 eq1762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1762
  have eq1946 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq985 eq1939
    | exact resolve eq1939 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq1948 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1946
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1946
    | exact resolve eq1946 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1946
  have eq1949 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq985 eq1948
    | exact resolve eq1948 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985 eq1948
  have eq1953 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1949 eq96
    | (have j0 := eq96 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq96 eq1949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq1949
  have eq1954 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1953
  have eq1956 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq986 eq1954
    | exact resolve eq1954 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986 eq1954
  have eq1959 : False := by grind
  exact eq1959

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq481 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq517 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq481 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq518 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq517 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq522 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq518 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq518 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq518 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq531 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq522 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq522
    | (have j0 := eq522 X0 X1
       grind)
    | exact resolve eq522 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq532 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq531 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq537 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq532 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq532
    | exact resolve eq532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq532 x y
       grind)
    | exact superpose eq532 eq16
    | exact resolve eq16 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq653 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq537 X0 (τ X1)
       grind)
    | exact superpose eq537 eq17
    | exact resolve eq17 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq537
  have eq679 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq653 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq653
    | exact resolve eq653 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq691 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq679 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq679
    | exact resolve eq679 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq715 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq548
       have i₂ := eq691 x y
       grind)
    | exact superpose eq691 eq548
    | exact resolve eq548 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq691
  have eq716 : False := by grind
  exact eq716

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq44 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq15
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq58
    | exact resolve eq58 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq58
  have eq81 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X0) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq81
    | (have j0 := eq81 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq81 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq336 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq152
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq152
    | (have j1 := eq81 (σ x) (σ y)
       grind)
    | (have r₁ := eq152
       have r₂ := eq81 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq152
       have r₂ := eq81 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq152 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq152
  have eq339 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq336
  have eq340 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq339
       grind)
    | exact superpose eq339 eq16
    | exact resolve eq16 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq341 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq340
       have r₂ := eq67 x
       grind)
    | exact resolve eq340 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq377 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq341
       grind)
    | exact superpose eq341 eq10
    | exact resolve eq10 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq394 : x = y := by
    first
    | (have i₁ := eq377
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq377
    | exact resolve eq377 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq438 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq394
       grind)
    | exact superpose eq394 eq16
    | exact resolve eq16 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq439 : False := by grind
  exact eq439

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_pyy_pyx_pyy_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq36 (τ X0)
       grind)
    | exact superpose eq36 eq18
    | exact resolve eq18 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq41 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq38
    | exact resolve eq38 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq41
    | exact resolve eq41 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq41
  have eq83 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq13
    | exact resolve eq13 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq98 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq95
  have eq284 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq98
    | exact resolve eq98 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq323 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq284
    | (have j0 := eq284 X0 X1
       grind)
    | exact resolve eq284 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq330 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq323 X0 X1
       have j1 := eq84 X1 X0
       grind)
    | (have r₁ := eq323 (σ X0) X0
       have r₂ := eq84 X0 (σ X0)
       grind)
    | (have r₁ := eq323 X1 X0
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq323 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq1068 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq330 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq330
    | exact resolve eq330 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1079 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq330 (σ X1) X0
       grind)
    | exact superpose eq330 eq15
    | (have j1 := eq330 (σ X1) X0
       grind)
    | exact resolve eq15 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq1092 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1068 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq1068
    | (have j0 := eq1068 X0 X1
       grind)
    | exact resolve eq1068 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1068
  have eq1112 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1092 X0 (τ X1)
       grind)
    | exact superpose eq1092 eq17
    | (have j1 := eq1092 X0 (τ X1)
       grind)
    | exact resolve eq17 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1092
  have eq6898 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1112 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1112
    | exact resolve eq1112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq6952 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6898 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6898
    | (have j0 := eq6898 X0 X1
       grind)
    | exact resolve eq6898 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6898
  have eq17453 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1079 x y
       grind)
    | exact superpose eq1079 eq16
    | (have j1 := eq1079 x y
       grind)
    | exact resolve eq16 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17611 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1079 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq17654 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq17453
       have i₂ := eq6952 y x
       grind)
    | exact superpose eq6952 eq17453
    | (have j1 := eq6952 y x
       grind)
    | (have r₁ := eq17453
       have r₂ := eq6952 y x
       grind)
    | exact resolve eq17453 eq6952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17655 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq17654
  have eq17659 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op x x) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq17655
       grind)
    | exact superpose eq17655 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq17655
       grind)
    | exact resolve eq13 eq17655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17655
  have eq17677 : (M.op x x) = (M.op y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq17659
  have eq214710 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq17677
       grind)
    | exact superpose eq17677 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq17677
       grind)
    | exact resolve eq12 eq17677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17677
  have eq214758 : (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq214710
  have eq288233 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17611 x y
       have i₂ := eq214758
       grind)
    | exact superpose eq214758 eq17611
    | (have j0 := eq17611 x y
       grind)
    | exact resolve eq17611 eq214758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17611 eq214758
  have eq288313 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq288233
  have eq288314 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq288313
  have eq288996 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17453
       have i₂ := eq288314
       grind)
    | exact superpose eq288314 eq17453
    | exact resolve eq17453 eq288314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17453 eq288314
  have eq289047 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq288996
  have eq289048 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq289047
  have eq289052 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq289048
       grind)
    | exact superpose eq289048 eq16
    | exact resolve eq16 eq289048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289053 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq83 x (σ y)
       have i₂ := eq289048
       grind)
    | exact superpose eq289048 eq83
    | (have j0 := eq83 x (σ y)
       grind)
    | (have r₁ := eq83 x (σ y)
       have r₂ := eq289048
       grind)
    | exact resolve eq83 eq289048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq289120 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by grind
  clear eq289053
  have eq289124 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq289120
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq289120
    | exact resolve eq289120 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289120
  have eq298126 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq84 x (σ y)
       have i₂ := eq289124
       grind)
    | exact superpose eq289124 eq84
    | (have j0 := eq84 x (σ y)
       grind)
    | (have r₁ := eq84 x (σ y)
       have r₂ := eq289124
       grind)
    | exact resolve eq84 eq289124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq289124
  have eq298192 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq298126
  have eq298225 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq298192
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq298192
    | exact resolve eq298192 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298192
  have eq298276 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq298225
       have i₂ := eq289048
       grind)
    | exact superpose eq289048 eq298225
    | exact resolve eq298225 eq289048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289048 eq298225
  have eq298277 : (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq298276
  have eq298329 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq6952 y x
       have i₂ := eq298277
       grind)
    | exact superpose eq298277 eq6952
    | (have j0 := eq6952 y x
       grind)
    | exact resolve eq6952 eq298277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6952 eq298277
  have eq298728 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq298329
       have r₂ := eq289052
       grind)
    | exact resolve eq298329 eq289052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298329
  have eq299534 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq289052
       have i₂ := eq298728
       grind)
    | exact superpose eq298728 eq289052
    | exact resolve eq289052 eq298728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289052 eq298728
  have eq299571 : False := by grind
  exact eq299571

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pxy_pxy_pxx_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq288 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq288 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq288 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq288 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq300 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq289 (σ X0)
       grind)
    | exact superpose eq289 eq15
    | exact resolve eq15 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq289 (τ X0)
       grind)
    | exact superpose eq289 eq31
    | exact resolve eq31 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq313 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq306 X0
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq306
    | exact resolve eq306 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq319 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq300 X0
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq300
    | exact resolve eq300 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq300
  have eq800 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq823 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq800 X0 X1
       have i₂ := eq319 X0
       grind)
    | exact superpose eq319 eq800
    | (have j0 := eq800 X0 X1
       grind)
    | exact resolve eq800 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq4725 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq823 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq823
    | exact resolve eq823 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq4837 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4725 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq4725
    | (have j0 := eq4725 X0 X1
       grind)
    | exact resolve eq4725 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4725
  have eq4840 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4837 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq4837 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq4837 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4837
  have eq4841 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4840 X0 X1
       have i₂ := eq313 X0
       grind)
    | exact superpose eq313 eq4840
    | (have j0 := eq4840 X0 X1
       grind)
    | exact resolve eq4840 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq4840
  have eq4842 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4841 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4841
    | (have j0 := eq4841 X0 X1
       grind)
    | exact resolve eq4841 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4841
  have eq4843 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4842 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4842
    | exact resolve eq4842 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4854 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4842 (σ X0) X1
       grind)
    | exact superpose eq4842 eq15
    | (have j1 := eq4842 (σ X0) X1
       grind)
    | exact resolve eq15 eq4842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4842
  have eq4873 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4854 X0 X1
       have i₂ := eq319 X0
       grind)
    | exact superpose eq319 eq4854
    | (have j0 := eq4854 X0 X1
       grind)
    | exact resolve eq4854 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4854
  have eq4891 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq4843 (τ X1) X0
       grind)
    | exact superpose eq4843 eq18
    | (have j1 := eq4843 (τ X1) X0
       grind)
    | exact resolve eq18 eq4843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4843
  have eq5029 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4891 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4891
    | exact resolve eq4891 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4891
  have eq5079 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5029 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5029
    | (have j0 := eq5029 X0 X1
       grind)
    | exact resolve eq5029 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5029
  have eq11920 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4873 x y
       grind)
    | exact superpose eq4873 eq16
    | (have j1 := eq4873 x y
       grind)
    | exact resolve eq16 eq4873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12068 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4873 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4873
  have eq12100 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11920
       have i₂ := eq5079 y x
       grind)
    | exact superpose eq5079 eq11920
    | (have j1 := eq5079 y x
       grind)
    | (have r₁ := eq11920
       have r₂ := eq5079 y x
       grind)
    | exact resolve eq11920 eq5079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11920
  have eq12101 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq12100
  have eq12105 : x ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq12101
       grind)
    | exact superpose eq12101 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq12101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12106 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq12101
       grind)
    | exact superpose eq12101 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12101
       grind)
    | exact resolve eq13 eq12101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12101
  have eq12131 : x = (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq12106
  have eq12132 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq12105
       have r₂ := eq12131
       grind)
    | exact resolve eq12105 eq12131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12105 eq12131
  have eq12158 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12068 x y
       have i₂ := eq12132
       grind)
    | exact superpose eq12132 eq12068
    | (have j0 := eq12068 x y
       grind)
    | exact resolve eq12068 eq12132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12068 eq12132
  have eq12198 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq12158
  have eq12199 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq12198
  have eq12462 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12199
       grind)
    | exact superpose eq12199 eq16
    | exact resolve eq16 eq12199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12465 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq12199
       grind)
    | exact superpose eq12199 eq12
    | exact resolve eq12 eq12199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12466 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq12199
       grind)
    | exact superpose eq12199 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq12199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12199
  have eq12492 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq12466
       have r₂ := eq319 x
       grind)
    | exact resolve eq12466 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12466
  have eq12493 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12465
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq12465
    | exact resolve eq12465 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12465
  have eq12495 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12492
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq12492
    | exact resolve eq12492 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12492
  have eq12496 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12495
       have i₂ := eq319 x
       grind)
    | exact superpose eq319 eq12495
    | exact resolve eq12495 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq12495
  have eq12497 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq12496
       have r₂ := eq12493
       grind)
    | exact resolve eq12496 eq12493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12493 eq12496
  have eq12505 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq5079 y x
       have i₂ := eq12497
       grind)
    | exact superpose eq12497 eq5079
    | (have j0 := eq5079 y x
       grind)
    | exact resolve eq5079 eq12497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5079 eq12497
  have eq12567 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq12505
       have r₂ := eq12462
       grind)
    | exact resolve eq12505 eq12462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12505
  have eq12584 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12462
       have i₂ := eq12567
       grind)
    | exact superpose eq12567 eq12462
    | exact resolve eq12462 eq12567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12462 eq12567
  have eq12613 : False := by grind
  exact eq12613

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_pyx_pxy_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq502 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq532 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq504 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq537 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq532 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq532 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq532 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq532 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq539 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq502 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq502 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq502 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq546 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq537 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq537
    | (have j0 := eq537 X0 X1
       grind)
    | exact resolve eq537 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq547 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq546 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq548 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq539 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq539
    | (have j0 := eq539 X0 X1
       grind)
    | exact resolve eq539 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq549 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq548 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq552 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq549 X0 X1
       have j1 := eq547 X0 X1
       grind)
    | (have r₁ := eq549 X0 X1
       have r₂ := eq547 X0 X1
       grind)
    | exact resolve eq549 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq549
  have eq553 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq552 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq552
    | exact resolve eq552 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq552 x y
       grind)
    | exact superpose eq552 eq16
    | exact resolve eq16 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq683 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq553 X0 (τ X1)
       grind)
    | exact superpose eq553 eq17
    | exact resolve eq17 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq553
  have eq699 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq683
    | exact resolve eq683 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq706 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq699
    | exact resolve eq699 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq718 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq564
       have i₂ := eq706 x y
       grind)
    | exact superpose eq706 eq564
    | exact resolve eq564 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq706
  have eq719 : False := by grind
  exact eq719
