import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_x_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq265 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq266 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq279 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq268 (σ X0)
       grind)
    | exact superpose eq268 eq15
    | exact resolve eq15 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq279
    | exact resolve eq279 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq279
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq345 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq344 X0 X1
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq344 X0 X1
       grind)
    | exact resolve eq343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq344
  have eq385 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq345
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq418 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq385 X0 X1
       grind)
    | exact superpose eq385 eq9
    | (have j1 := eq385 X0 X1
       grind)
    | exact resolve eq9 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq941 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq418 X0 X1
       grind)
    | exact superpose eq418 eq9
    | (have j1 := eq418 X0 X1
       grind)
    | exact resolve eq9 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq951 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq941 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq941 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq941 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq979 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq951 (σ X1) (σ X0)
       grind)
    | exact superpose eq951 eq15
    | exact resolve eq15 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq979 X0 X1
       have i₂ := eq951 X1 X0
       grind)
    | exact superpose eq951 eq979
    | exact resolve eq979 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951 eq979
  have eq1389 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1006 x y
       grind)
    | exact superpose eq1006 eq16
    | (have r₁ := eq16
       have r₂ := eq1006 x y
       grind)
    | exact resolve eq16 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq1410 : False := by grind
  exact eq1410

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxx_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq265 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq266 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq279 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq268 (σ X0)
       grind)
    | exact superpose eq268 eq15
    | exact resolve eq15 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq279
    | exact resolve eq279 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq279
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq345 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq344 X0 X1
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq344 X0 X1
       grind)
    | exact resolve eq343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq344
  have eq386 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq345
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq419 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq386 X0 X1
       grind)
    | exact superpose eq386 eq9
    | (have j1 := eq386 X0 X1
       grind)
    | exact resolve eq9 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq560 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq419 X0 X1
       grind)
    | exact superpose eq419 eq9
    | (have j1 := eq419 X0 X1
       grind)
    | exact resolve eq9 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq564 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq560 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq560 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq560 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq609 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq564 (σ X0) (σ X1)
       grind)
    | exact superpose eq564 eq15
    | exact resolve eq15 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq609 X0 X1
       have i₂ := eq564 X0 X1
       grind)
    | exact superpose eq564 eq609
    | exact resolve eq609 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq609
  have eq952 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq636 x y
       grind)
    | exact superpose eq636 eq16
    | (have r₁ := eq16
       have r₂ := eq636 x y
       grind)
    | exact resolve eq16 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq968 : False := by grind
  exact eq968

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxy_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq265 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq266 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq279 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq268 (σ X0)
       grind)
    | exact superpose eq268 eq15
    | exact resolve eq15 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq279
    | exact resolve eq279 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq279
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq345 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq344 X0 X1
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq344 X0 X1
       grind)
    | exact resolve eq343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq344
  have eq385 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq345
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq418 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq385 X0 X1
       grind)
    | exact superpose eq385 eq9
    | (have j1 := eq385 X0 X1
       grind)
    | exact resolve eq9 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq945 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq418 X0 X1
       grind)
    | exact superpose eq418 eq9
    | (have j1 := eq418 X0 X1
       grind)
    | exact resolve eq9 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq955 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq945 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq945 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq945 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq979 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq955 (σ X0) (σ X1)
       grind)
    | exact superpose eq955 eq15
    | exact resolve eq15 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1010 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq979 X0 X1
       have i₂ := eq955 X0 X1
       grind)
    | exact superpose eq955 eq979
    | exact resolve eq979 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq979
  have eq1386 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1010 x y
       grind)
    | exact superpose eq1010 eq16
    | (have r₁ := eq16
       have r₂ := eq1010 x y
       grind)
    | exact resolve eq16 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1407 : False := by grind
  exact eq1407

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
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
  have eq68 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq71 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq71 y x
       grind)
    | exact superpose eq71 eq68
    | (have j1 := eq71 y x
       grind)
    | exact resolve eq68 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq109 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq116 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq43
    | exact resolve eq43 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq123 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq116
    | exact resolve eq116 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq116
  have eq834 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq101 eq71
    | (have j0 := eq71 (σ y) (σ x)
       grind)
    | exact resolve eq71 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq835 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq834
    | exact resolve eq834 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq838 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq835
       have r₂ := eq27
       grind)
    | exact resolve eq835 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq840 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq838
    | exact resolve eq838 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq842 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq840 eq110
    | (have r₁ := eq110
       have r₂ := eq840
       grind)
    | exact resolve eq110 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq845 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq840 eq14
    | exact resolve eq14 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq849 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq842
  have eq875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq849 eq101
    | exact resolve eq101 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq878 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq875
  have eq880 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq878
       have r₂ := eq27
       grind)
    | exact resolve eq878 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq933 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq880
       grind)
    | exact superpose eq880 eq109
    | (have r₁ := eq109
       have r₂ := eq880
       grind)
    | exact resolve eq109 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq880
       grind)
    | exact superpose eq880 eq123
    | exact resolve eq123 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq939 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq880
       grind)
    | exact superpose eq880 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq941 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq933
  have eq943 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq934
    | exact resolve eq934 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq1007 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq941
       grind)
    | exact superpose eq941 eq68
    | exact resolve eq68 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq1009 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1007
    | exact resolve eq1007 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1009 eq71
    | (have j0 := eq71 (σ y) (σ x)
       grind)
    | exact resolve eq71 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq1017 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1014
    | exact resolve eq1014 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1020 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1017
       have r₂ := eq27
       grind)
    | exact resolve eq1017 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1022 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1020
    | exact resolve eq1020 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1022 eq943
    | exact resolve eq943 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1038 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1025
  have eq1041 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1038
       have r₂ := eq27
       grind)
    | exact resolve eq1038 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1262 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq939 X0
       grind)
    | (have r₁ := eq939 X0
       have r₂ := eq1041
       grind)
    | exact resolve eq939 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939 eq1041
  have eq1269 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq1262 y
       grind)
    | exact superpose eq1262 eq68
    | exact resolve eq68 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1288 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1269
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1269
    | exact resolve eq1269 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1269
  have eq1290 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1288
    | exact resolve eq1288 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1295 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1290 eq71
    | (have j0 := eq71 (σ y) (σ x)
       grind)
    | exact resolve eq71 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1295
    | exact resolve eq1295 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq1301 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1298
       have r₂ := eq27
       grind)
    | exact resolve eq1298 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1303 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1301
    | exact resolve eq1301 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq1368 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1303 eq943
    | exact resolve eq943 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943 eq1303
  have eq1381 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1368
  have eq1384 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1381
       have r₂ := eq27
       grind)
    | exact resolve eq1381 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1388 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1384 eq27
    | exact resolve eq27 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1670 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ x)))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1384 eq845
    | exact resolve eq845 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845 eq1384
  have eq1785 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1670 eq14
    | exact resolve eq14 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq1803 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1785 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1785
       grind)
    | exact resolve eq13 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785
  have eq1804 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1803 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803
  have eq2102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1804 eq101
    | exact resolve eq101 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq1804
  have eq2113 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq2102
  have eq2120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq2113
    | exact resolve eq2113 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113
  have eq2124 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2120
       have r₂ := eq27
       grind)
    | exact resolve eq2120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2120
  have eq2128 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq2124
       grind)
    | exact superpose eq2124 eq109
    | (have r₁ := eq109
       have r₂ := eq2124
       grind)
    | exact resolve eq109 eq2124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq2129 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq2124
       grind)
    | exact superpose eq2124 eq123
    | exact resolve eq123 eq2124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq2124
  have eq2136 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq2128
  have eq2138 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq2129
    | exact resolve eq2129 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2129
  have eq2289 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq2136
       grind)
    | exact superpose eq2136 eq68
    | exact resolve eq68 eq2136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq2136
  have eq2292 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2289
    | exact resolve eq2289 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2289
  have eq2300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2292 eq71
    | (have j0 := eq71 (σ y) (σ x)
       grind)
    | exact resolve eq71 eq2292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq2292
  have eq2301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2300
    | exact resolve eq2300 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2300
  have eq2304 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2301
       have r₂ := eq27
       grind)
    | exact resolve eq2301 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2301
  have eq2306 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2138 eq2304
    | exact resolve eq2304 eq2138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138 eq2304
  have eq2308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2306
    | exact resolve eq2306 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2306
  have eq2310 : x = (M.op x y) := by
    first
    | (have r₁ := eq2308
       have r₂ := eq27
       grind)
    | exact resolve eq2308 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2308
  have eq2312 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2310 eq20
    | exact resolve eq20 eq2310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2310
  have eq2347 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2312
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2312
    | exact resolve eq2312 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2312
  have eq2351 : False := by grind
  exact eq2351

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_y_pxy_Equation413 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq53 : y = (M.op y (M.op y (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq90 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq94 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq90
  have eq95 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq94
  have eq116 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq119 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by grind
  clear eq116
  have eq120 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq119
  have eq126 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq120 eq16
    | exact resolve eq16 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq181 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq519 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq72
  have eq634 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq519 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq519
    | (have j0 := eq519 x X0
       grind)
    | exact resolve eq519 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq3666 : ∀ X0 : G, (σ (k X0 y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq181 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq4309 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq634 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq634
    | (have j0 := eq634 y
       grind)
    | exact resolve eq634 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq4318 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4309
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq4309
    | exact resolve eq4309 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4309
  have eq4337 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq4318
    | exact resolve eq4318 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4318
  have eq4345 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4337
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq4337
    | exact resolve eq4337 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4337
  have eq4350 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq4345
    | exact resolve eq4345 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4345
  have eq9996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq84 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9997 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9996
    | exact resolve eq9996 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9996
  have eq10008 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq9997
       have r₂ := eq28
       grind)
    | exact resolve eq9997 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9997
  have eq10012 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq10008
    | exact resolve eq10008 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10008
  have eq10140 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq10012 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq10012
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq10012
       grind)
    | exact resolve eq12 eq10012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10012
  have eq14263 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq10140
    | (have j0 := eq10140 (σ x)
       grind)
    | (have r₁ := eq10140 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq10140 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10140
  have eq14264 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq14263
  have eq14265 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq14264
  have eq14275 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq14265 eq84
    | exact resolve eq84 eq14265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq14265
  have eq14287 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14275
  have eq14308 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq14287
       grind)
    | exact superpose eq14287 eq95
    | exact resolve eq95 eq14287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14317 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ y = (k X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq14287
       grind)
    | exact superpose eq14287 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14287
       grind)
    | exact resolve eq12 eq14287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14287
  have eq14331 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq14308
    | exact resolve eq14308 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14308
  have eq90762 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14317 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14317
    | (have j0 := eq14317 x
       grind)
    | (have r₁ := eq14317 x
       have r₂ := eq19
       grind)
    | exact resolve eq14317 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14317
  have eq90765 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq90762
  have eq90766 : y = (k x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq90765
  have eq90770 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq90766
       grind)
    | exact superpose eq90766 eq49
    | exact resolve eq49 eq90766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq90766
  have eq90858 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq90770
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq90770
    | exact resolve eq90770 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90770
  have eq90903 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq90858 eq4350
    | exact resolve eq4350 eq90858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4350 eq90858
  have eq90957 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq90903
  have eq91002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq90957 eq14331
    | exact resolve eq14331 eq90957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90957
  have eq91112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq91002
  have eq91128 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq91112
       have r₂ := eq28
       grind)
    | exact resolve eq91112 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91112
  have eq91135 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq91128 eq54
    | exact resolve eq54 eq91128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq91128
  have eq93131 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq91135 eq14
    | exact resolve eq14 eq91135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91135
  have eq93187 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq93131 eq14331
    | exact resolve eq14331 eq93131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14331 eq93131
  have eq93307 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq93187
  have eq94177 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq93307 eq30
    | exact resolve eq30 eq93307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93307
  have eq94307 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq94177
    | exact resolve eq94177 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94177
  have eq94308 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq94307
  have eq94329 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq94308 eq30
    | exact resolve eq30 eq94308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94345 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq94308 eq126
    | exact resolve eq126 eq94308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq94683 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq159 eq94345
    | exact resolve eq94345 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94345
  have eq94697 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq94329
    | exact resolve eq94329 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94329
  have eq94718 : y = (M.op y (M.op y (M.op y y))) ∨ x = y := by
    first
    | exact superpose eq94697 eq53
    | exact resolve eq53 eq94697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq107427 : y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq94718
       grind)
    | exact superpose eq94718 eq14
    | exact resolve eq14 eq94718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94718
  have eq107444 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq107427
       grind)
    | exact superpose eq107427 eq95
    | exact resolve eq95 eq107427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107536 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = X0 ∨ y = (k X0 y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq107427
       grind)
    | exact superpose eq107427 eq12
    | (have j0 := eq12 y X0
       grind)
    | exact resolve eq12 eq107427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107427
  have eq107638 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq107444
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq107444
    | exact resolve eq107444 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107444
  have eq107644 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq94308 eq107638
    | exact resolve eq107638 eq94308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94308
  have eq107849 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq107644
  have eq108765 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq107849 eq159
    | exact resolve eq159 eq107849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq107849
  have eq108818 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq31 eq108765
    | exact resolve eq108765 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq108765
  have eq108955 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq108818 eq94683
    | exact resolve eq94683 eq108818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94683 eq108818
  have eq108965 : (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq108955
  have eq109831 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq108965
       grind)
    | exact superpose eq108965 eq95
    | exact resolve eq95 eq108965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq108965
  have eq109891 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq109831
    | exact resolve eq109831 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109831
  have eq2508151 : y ≠ (M.op x y) ∨ x = y ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq107536 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107536
    | (have j0 := eq107536 x
       grind)
    | exact resolve eq107536 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107536
  have eq2508156 : y ≠ (M.op x y) ∨ x = y ∨ y = (k x y) := by grind
  clear eq2508151
  have eq2508157 : y = (k x y) ∨ x = y := by
    first
    | (have r₁ := eq2508156
       have r₂ := eq94697
       grind)
    | exact resolve eq2508156 eq94697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94697 eq2508156
  have eq2511299 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3666 x
       have i₂ := eq2508157
       grind)
    | exact superpose eq2508157 eq3666
    | (have j0 := eq3666 x
       grind)
    | exact resolve eq3666 eq2508157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666 eq2508157
  have eq2511385 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2511299
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2511299
    | exact resolve eq2511299 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511299
  have eq2511494 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2511385
       have r₂ := eq107638
       grind)
    | exact resolve eq2511385 eq107638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107638 eq2511385
  have eq2511539 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2511494
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2511494
    | exact resolve eq2511494 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511494
  have eq2511564 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq2511539
    | exact resolve eq2511539 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511539
  have eq2511582 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2511564
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2511564
    | exact resolve eq2511564 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511564
  have eq2546879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2511582 eq109891
    | exact resolve eq109891 eq2511582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109891 eq2511582
  have eq2547182 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2546879
  have eq2547287 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2547182
       have r₂ := eq28
       grind)
    | exact resolve eq2547182 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2547182
  have eq2550308 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2547287 eq30
    | exact resolve eq30 eq2547287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2547287
  have eq2553008 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq2550308
    | exact resolve eq2550308 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2550308
  have eq2553009 : x = y := by grind
  clear eq2553008
  have eq2553124 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2553009
       grind)
    | exact superpose eq2553009 eq19
    | exact resolve eq19 eq2553009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2553125 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2553009
       grind)
    | exact superpose eq2553009 eq25
    | exact resolve eq25 eq2553009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2553009
  have eq2554294 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2553125
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2553125
    | exact resolve eq2553125 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2553125
  have eq2554466 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2554294 eq27
    | exact resolve eq27 eq2554294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2554294
  have eq2556665 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2554466 eq67
    | exact resolve eq67 eq2554466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2554466
  have eq2556774 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2556665
       have i₂ := eq2553124
       grind)
    | exact superpose eq2553124 eq2556665
    | exact resolve eq2556665 eq2553124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2553124 eq2556665
  have eq2556850 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2556774 eq15
    | exact resolve eq15 eq2556774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2556774
  have eq2557783 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq2556850
    | exact resolve eq2556850 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2556850
  have eq2558031 : False := by grind
  exact eq2558031

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation413 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq462 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq465 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  clear eq18
  have eq2994 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq465 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq465
    | exact resolve eq465 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq3037 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2994 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2994
    | (have j0 := eq2994 X0 X1
       grind)
    | exact resolve eq2994 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2994
  have eq3047 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq3037 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq3037 X0 X1
       grind)
    | exact superpose eq3037 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq3037 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq3037 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq3037 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq3037 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq3037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3076 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq3037 X1 (τ X0)
       grind)
    | (have i₁ := eq30 X0
       have i₂ := eq3037 (τ X0) (τ X0)
       grind)
    | exact superpose eq3037 eq30
    | (have j1 := eq3037 X1 (τ X0)
       grind)
    | exact resolve eq30 eq3037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3037
  have eq3083 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3047 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3047
  have eq3084 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3083 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3083
  have eq3086 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3076 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq3076
    | (have j0 := eq3076 X0 X1
       grind)
    | exact resolve eq3076 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3076
  have eq3187 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq3084 X0 X1
       grind)
    | exact superpose eq3084 eq10
    | (have j1 := eq3084 X0 X1
       grind)
    | exact resolve eq10 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3084
  have eq3231 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3187 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3187
    | (have j0 := eq3187 X0 X1
       grind)
    | exact resolve eq3187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3187
  have eq3263 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3231 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3231
    | (have j0 := eq3231 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq3231 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3231
  have eq3421 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3263 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq3263
    | (have j0 := eq3263 X0 X1
       grind)
    | exact resolve eq3263 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3263
  have eq3561 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq462 (σ x) y
       grind)
    | exact superpose eq462 eq16
    | (have j1 := eq462 (σ x) y
       grind)
    | (have r₁ := eq16
       have r₂ := eq462 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq3574 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3561
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq3561
    | exact resolve eq3561 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3561
  have eq3585 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3574
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3574
    | exact resolve eq3574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3574
  have eq7066 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3086 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3086
    | exact resolve eq3086 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3086
  have eq7177 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7066 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7066
    | (have j0 := eq7066 X0 X1
       grind)
    | exact resolve eq7066 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7066
  have eq7189 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7177 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq7177
    | (have j0 := eq7177 X0 X1
       grind)
    | exact resolve eq7177 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7177
  have eq15446 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3421 y x
       grind)
    | exact superpose eq3421 eq16
    | (have j1 := eq3421 y x
       grind)
    | exact resolve eq16 eq3421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421
  have eq15552 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq15446
       have i₂ := eq7189 x y
       grind)
    | exact superpose eq7189 eq15446
    | (have j1 := eq7189 x y
       grind)
    | (have r₁ := eq15446
       have r₂ := eq7189 x y
       grind)
    | (have r₁ := eq15446
       have r₂ := eq7189 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq15446
       have r₂ := eq7189 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq15446 eq7189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7189 eq15446
  have eq15555 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq15552
  have eq15556 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq15555
  have eq15561 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15556
       grind)
    | exact superpose eq15556 eq16
    | exact resolve eq16 eq15556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15556
  have eq15562 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15561
       have r₂ := eq22 x
       grind)
    | exact resolve eq15561 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15561
  have eq15564 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15562
       grind)
    | exact superpose eq15562 eq10
    | exact resolve eq10 eq15562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15562
  have eq15628 : x = y ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq15564
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15564
    | exact resolve eq15564 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15564
  have eq15630 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15628
       grind)
    | exact superpose eq15628 eq16
    | exact resolve eq16 eq15628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15628
  have eq15631 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15630
       have r₂ := eq22 x
       grind)
    | exact resolve eq15630 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15630
  have eq15980 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3585
       have i₂ := eq15631
       grind)
    | exact superpose eq15631 eq3585
    | (have r₁ := eq3585
       have r₂ := eq15631
       grind)
    | exact resolve eq3585 eq15631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3585
  have eq15981 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq15631
       grind)
    | exact superpose eq15631 eq10
    | exact resolve eq10 eq15631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16027 : (σ x) = (σ y) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq15980
  have eq16047 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq15981
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq15981
    | exact resolve eq15981 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15981
  have eq16050 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq16047
       grind)
    | exact superpose eq16047 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16047
       grind)
    | exact resolve eq13 eq16047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16047
  have eq16054 : x = y ∨ (k y x) = (M.op x x) := by grind
  clear eq16050
  have eq16056 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16054
       grind)
    | exact superpose eq16054 eq16
    | exact resolve eq16 eq16054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16054
  have eq16057 : (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq16056
       have r₂ := eq22 x
       grind)
    | exact resolve eq16056 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16056
  have eq16968 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16027
       grind)
    | exact superpose eq16027 eq16
    | exact resolve eq16 eq16027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16027
  have eq17058 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16968
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq16968
    | exact resolve eq16968 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16968
  have eq17079 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq17058
       have r₂ := eq15631
       grind)
    | exact resolve eq17058 eq15631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17058
  have eq17080 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq17079
       have i₂ := eq16057
       grind)
    | exact superpose eq16057 eq17079
    | exact resolve eq17079 eq16057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16057 eq17079
  have eq17099 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq17080
       grind)
    | exact superpose eq17080 eq11
    | exact resolve eq11 eq17080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17080
  have eq17209 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17099
       grind)
    | exact superpose eq17099 eq16
    | exact resolve eq16 eq17099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17099
  have eq17231 : False := by grind
  exact eq17231

/-- `Equation4167`: `x ◇ y = ((y ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pyx_pxy_Equation4167 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4167 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4167.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X1 X1) X1) X0) := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op (M.op X0 X0) X0) X0) ∨ (M.op (M.op (M.op X0 X0) X0) X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op (M.op X0 X0) X0) X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq34
    | (have j0 := eq34 X0 X1
       grind)
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq35
    | (have j0 := eq35 X0 X1
       grind)
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq76 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq83 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq85 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq58 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq58 X0
       grind)
    | exact resolve eq12 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq93 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq90 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq90 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq486 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq83 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq520 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq486 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq486
    | (have j0 := eq486 X0 X1
       grind)
    | exact resolve eq486 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq777 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq76 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq76 X0
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq76 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq780 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq777 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq2936 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq780 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq780
    | exact resolve eq780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq3003 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2936 X0 X1
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq2936
    | (have j0 := eq2936 X0 X1
       grind)
    | exact resolve eq2936 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2936
  have eq3010 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3003 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3003
    | (have j0 := eq3003 X0 X0
       grind)
    | exact resolve eq3003 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq3060 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3010 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3010
  have eq3061 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3060 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3060
  have eq3285 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq3061 X0
       grind)
    | exact superpose eq3061 eq93
    | (have j0 := eq93 X0 X1
       grind)
    | exact resolve eq93 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq3292 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq779 X0
       have i₂ := eq3061 X0
       grind)
    | exact superpose eq3061 eq779
    | exact resolve eq779 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq3309 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq3061 (σ X0)
       grind)
    | exact superpose eq3061 eq15
    | exact resolve eq15 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3316 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0 X0
       have i₂ := eq3061 (τ X0)
       grind)
    | exact superpose eq3061 eq37
    | exact resolve eq37 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3337 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3316 X0
       have i₂ := eq3061 X0
       grind)
    | exact superpose eq3061 eq3316
    | exact resolve eq3316 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3316
  have eq3344 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3309 X0
       have i₂ := eq3061 X0
       grind)
    | exact superpose eq3061 eq3309
    | exact resolve eq3309 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3061 eq3309
  have eq3725 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq3344 X0
       grind)
    | exact superpose eq3344 eq9
    | exact resolve eq9 eq3344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9964 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3292 (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq3292
    | (have j1 := eq85 X1 X0
       grind)
    | exact resolve eq3292 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq3292
  have eq9973 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq9964 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9964
  have eq9984 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9973 X0 X1
       have i₂ := eq3337 (σ X0)
       grind)
    | exact superpose eq3337 eq9973
    | (have j0 := eq9973 X0 X1
       grind)
    | exact resolve eq9973 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9973
  have eq10007 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9984 X0 X1
       have i₂ := eq3344 X0
       grind)
    | exact superpose eq3344 eq9984
    | (have j0 := eq9984 X0 X1
       grind)
    | exact resolve eq9984 eq3344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9984
  have eq10020 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10007 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq10007
    | (have j0 := eq10007 X0 X1
       grind)
    | exact resolve eq10007 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10007
  have eq10025 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10020 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10020
    | (have j0 := eq10020 X0 X1
       grind)
    | exact resolve eq10020 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10020
  have eq10259 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (σ (τ X0)) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3337 X0
       have i₂ := eq10025 (τ X0) X1
       grind)
    | exact superpose eq10025 eq3337
    | (have j1 := eq10025 (τ X0) X1
       grind)
    | exact resolve eq3337 eq10025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3337 eq10025
  have eq10275 : ∀ X0 X1 : G, X0 = X1 ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10259 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10259
    | (have j0 := eq10259 X0 X1
       grind)
    | exact resolve eq10259 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10259
  have eq10309 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10275 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10275
    | (have j0 := eq10275 X0 X1
       grind)
    | exact resolve eq10275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10275
  have eq10335 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10309 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq10309
    | (have j0 := eq10309 X0 X1
       grind)
    | exact resolve eq10309 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq10309
  have eq10599 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X1) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq10335 X1 X0
       grind)
    | exact superpose eq10335 eq11
    | (have j1 := eq10335 (k X0 X1) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq10335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10335
  have eq10693 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X1 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10599 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq10599
    | (have j0 := eq10599 X0 X1
       grind)
    | exact resolve eq10599 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10599
  have eq10787 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10693 X1 (σ X0)
       have i₂ := eq3344 X0
       grind)
    | exact superpose eq3344 eq10693
    | (have j0 := eq10693 (τ (σ X0)) (τ (σ (M.op X0 X0)))
       grind)
    | exact resolve eq10693 eq3344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10693
  have eq10916 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10787 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq10787
    | (have j0 := eq10787 X0 X1
       grind)
    | exact resolve eq10787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10787
  have eq10932 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10916 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10916
    | (have j0 := eq10916 X0 X1
       grind)
    | exact resolve eq10916 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10916
  have eq11204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq10932 X1 (σ X0)
       grind)
    | exact superpose eq10932 eq15
    | (have j1 := eq10932 (k X0 X1) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq10932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10932
  have eq26780 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11204 x y
       grind)
    | exact superpose eq11204 eq16
    | (have j1 := eq11204 x y
       grind)
    | exact resolve eq16 eq11204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11204
  have eq26963 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq26780
       have i₂ := eq520 x y
       grind)
    | exact superpose eq520 eq26780
    | (have j1 := eq520 x y
       grind)
    | (have r₁ := eq26780
       have r₂ := eq520 x y
       grind)
    | (have r₁ := eq26780
       have r₂ := eq520 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq26780
       have r₂ := eq520 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq26780 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520 eq26780
  have eq26964 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq26963
  have eq26965 : x = y ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq26964
  have eq26968 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26965
       grind)
    | exact superpose eq26965 eq16
    | exact resolve eq16 eq26965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26965
  have eq26969 : (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq26968
       have r₂ := eq3344 x
       grind)
    | exact resolve eq26968 eq3344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26968
  have eq27097 : y = (τ (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq26969
       grind)
    | exact superpose eq26969 eq10
    | exact resolve eq10 eq26969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26969
  have eq27194 : x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq27097
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq27097
    | exact resolve eq27097 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27097
  have eq27219 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27194
       grind)
    | exact superpose eq27194 eq16
    | exact resolve eq16 eq27194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27194
  have eq27220 : y = (M.op y y) := by
    first
    | (have r₁ := eq27219
       have r₂ := eq3344 x
       grind)
    | exact resolve eq27219 eq3344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27219
  have eq27497 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq27220
       grind)
    | exact superpose eq27220 eq9
    | exact resolve eq9 eq27220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27498 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq27220
       grind)
    | exact superpose eq27220 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq27220
       grind)
    | exact resolve eq12 eq27220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27508 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq3285 y X0
       have i₂ := eq27220
       grind)
    | exact superpose eq27220 eq3285
    | (have j0 := eq3285 y X0
       grind)
    | exact resolve eq3285 eq27220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285
  have eq27515 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ y) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq3725 y X0
       have i₂ := eq27220
       grind)
    | exact superpose eq27220 eq3725
    | exact resolve eq3725 eq27220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3725
  have eq27530 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq27508 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27508
  have eq27532 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq27498 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27498
  have eq27540 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq27515 X0
       have i₂ := eq3344 y
       grind)
    | exact superpose eq3344 eq27515
    | exact resolve eq27515 eq3344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27515
  have eq27553 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq27497 X0
       have i₂ := eq27220
       grind)
    | exact superpose eq27220 eq27497
    | exact resolve eq27497 eq27220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27497
  have eq27558 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq27540 X0
       have i₂ := eq27220
       grind)
    | exact superpose eq27220 eq27540
    | exact resolve eq27540 eq27220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27540
  have eq28865 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq27530 (σ X0)
       grind)
    | exact superpose eq27530 eq15
    | exact resolve eq15 eq27530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27530
  have eq28944 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq28865 X0
       have i₂ := eq27532 X0
       grind)
    | exact superpose eq27532 eq28865
    | exact resolve eq28865 eq27532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28865
  have eq29343 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ (M.op X0 (σ y)) = (k X0 (M.op (σ y) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq36 (σ y) x
       have i₂ := eq27558 (M.op (σ y) (σ y))
       grind)
    | exact superpose eq27558 eq36
    | exact resolve eq36 eq27558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq27558
  have eq29412 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op (σ y) (σ (M.op y y))) ∨ (M.op X0 (σ y)) = (k X0 (M.op (σ y) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq29343 X0
       have i₂ := eq3344 y
       grind)
    | exact superpose eq3344 eq29343
    | (have j0 := eq29343 X0
       grind)
    | exact resolve eq29343 eq3344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29343
  have eq29449 : ∀ X0 : G, (σ (M.op y y)) ≠ (σ (M.op y (M.op y y))) ∨ (M.op X0 (σ y)) = (k X0 (M.op (σ y) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq29412 X0
       have i₂ := eq28944 (M.op y y)
       grind)
    | exact superpose eq28944 eq29412
    | (have j0 := eq29412 X0
       grind)
    | exact resolve eq29412 eq28944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29412
  have eq29472 : ∀ X0 : G, (σ y) ≠ (σ (M.op y y)) ∨ (M.op X0 (σ y)) = (k X0 (M.op (σ y) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq29449 X0
       have i₂ := eq27220
       grind)
    | exact superpose eq27220 eq29449
    | (have j0 := eq29449 X0
       grind)
    | exact resolve eq29449 eq27220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29449
  have eq29484 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (M.op (σ y) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq29472 X0
       have i₂ := eq27220
       grind)
    | exact superpose eq27220 eq29472
    | (have j0 := eq29472 X0
       grind)
    | exact resolve eq29472 eq27220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29472
  have eq29485 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (M.op (σ y) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq29484 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29484
  have eq29494 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (M.op (σ y) (σ (M.op y y)))) := by
    intro X0
    first
    | (have i₁ := eq29485 X0
       have i₂ := eq3344 y
       grind)
    | exact superpose eq3344 eq29485
    | exact resolve eq29485 eq3344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3344 eq29485
  have eq29502 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ (M.op y (M.op y y)))) := by
    intro X0
    first
    | (have i₁ := eq29494 X0
       have i₂ := eq28944 (M.op y y)
       grind)
    | exact superpose eq28944 eq29494
    | exact resolve eq29494 eq28944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28944 eq29494
  have eq29509 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq29502 X0
       have i₂ := eq27220
       grind)
    | exact superpose eq27220 eq29502
    | exact resolve eq29502 eq27220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29502
  have eq29515 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq29509 X0
       have i₂ := eq27220
       grind)
    | exact superpose eq27220 eq29509
    | exact resolve eq29509 eq27220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27220 eq29509
  have eq30053 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq29515 (σ X0)
       grind)
    | exact superpose eq29515 eq15
    | exact resolve eq15 eq29515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29515
  have eq30130 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq30053 X0
       have i₂ := eq27532 X0
       grind)
    | exact superpose eq27532 eq30053
    | exact resolve eq30053 eq27532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27532 eq30053
  have eq33031 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30130 x
       grind)
    | exact superpose eq30130 eq16
    | exact resolve eq16 eq30130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30130
  have eq33128 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq33031
       have i₂ := eq27553 x
       grind)
    | exact superpose eq27553 eq33031
    | exact resolve eq33031 eq27553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27553 eq33031
  have eq33129 : False := by grind
  exact eq33129

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_y_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq25 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq22 (M.op X0 X1)
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq34
    | exact resolve eq34 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | (have r₁ := eq57 X0 X0
       have r₂ := eq22 X0
       grind)
    | exact resolve eq57 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq70 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq79 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq88 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op (τ X1) (τ X1)) = X0 := by
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
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq93 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq22 (σ X1)
       grind)
    | exact superpose eq22 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq97 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq22 (τ X1)
       grind)
    | exact superpose eq22 eq93
    | (have j0 := eq93 X0 X1
       grind)
    | exact resolve eq93 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq99 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq79
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq79 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq130 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 X1
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq122
    | (have j0 := eq122 X0 X1
       grind)
    | exact resolve eq122 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq133 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq130 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq130
    | (have j0 := eq130 X0 X1
       grind)
    | exact resolve eq130 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq134 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq96 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq134
    | (have j0 := eq134 X0 X1
       grind)
    | exact resolve eq134 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq497 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq148
    | exact resolve eq148 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq738 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq774 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq738 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq738
    | (have j0 := eq738 X0 X1
       grind)
    | exact resolve eq738 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq4665 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k x (τ (σ y))) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq133 x (σ y)
       grind)
    | exact superpose eq133 eq16
    | (have j1 := eq133 x (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq133 (M.op x y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4673 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) X1
       have i₂ := eq133 X0 X1
       grind)
    | exact superpose eq133 eq59
    | (have j0 := eq59 (σ X0) X1
       have j1 := eq133 X0 X1
       grind)
    | (have r₁ := eq59 (σ X0) X1
       have r₂ := eq133 X0 X1
       grind)
    | (have r₁ := eq59 (σ X0) X1
       have r₂ := eq133 X0 (M.op (σ X0) X1)
       grind)
    | exact resolve eq59 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq133
  have eq4687 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4673 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4673
  have eq4688 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4687 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4687
  have eq4695 : (σ (M.op x y)) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4665
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4665
    | exact resolve eq4665 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4665
  have eq4700 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4688 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4688
    | exact resolve eq4688 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4745 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ X1) X0
       have i₂ := eq4688 X1 (σ X0)
       grind)
    | exact superpose eq4688 eq70
    | (have j1 := eq4688 X0 (σ X1)
       grind)
    | exact resolve eq70 eq4688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq4688
  have eq4805 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4745 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4745
    | (have j0 := eq4745 X0 X1
       grind)
    | exact resolve eq4745 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4745
  have eq4816 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4700 X0 X1
       have i₂ := eq99 X1 X0
       grind)
    | exact superpose eq99 eq4700
    | (have j0 := eq4700 X0 X1
       grind)
    | exact resolve eq4700 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq4700
  have eq4839 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4805 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4805
    | (have j0 := eq4805 X0 X1
       grind)
    | exact resolve eq4805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4805
  have eq4846 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4839 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4839
    | (have j0 := eq4839 X0 X1
       grind)
    | exact resolve eq4839 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4839
  have eq4876 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4816 X0 X1
       grind)
    | exact superpose eq4816 eq11
    | (have j1 := eq4816 X0 X1
       grind)
    | exact resolve eq11 eq4816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4816
  have eq4984 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4876 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4876
    | (have j0 := eq4876 X0 X1
       grind)
    | exact resolve eq4876 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4876
  have eq5118 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq4984 (τ X0) X1
       grind)
    | exact superpose eq4984 eq18
    | (have j1 := eq4984 (τ X0) X1
       grind)
    | exact resolve eq18 eq4984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4984
  have eq5696 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4846 X1 X0
       grind)
    | exact superpose eq4846 eq11
    | (have j1 := eq4846 X1 X0
       grind)
    | exact resolve eq11 eq4846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4846
  have eq6750 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5696 x y
       grind)
    | exact superpose eq5696 eq16
    | (have j1 := eq5696 x y
       grind)
    | exact resolve eq16 eq5696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5696
  have eq6818 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6750
       have i₂ := eq497 y x
       grind)
    | exact superpose eq497 eq6750
    | (have j1 := eq497 y x
       grind)
    | (have r₁ := eq6750
       have r₂ := eq497 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6750
       have r₂ := eq497 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6750 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq6750
  have eq6823 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6818
  have eq6930 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6823
       grind)
    | exact superpose eq6823 eq16
    | exact resolve eq16 eq6823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6823
  have eq6931 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6930
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq6930
    | exact resolve eq6930 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6930
  have eq6932 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6931
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq6931
    | exact resolve eq6931 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6931
  have eq6933 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6932
  have eq6937 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25 x y
       have i₂ := eq6933
       grind)
    | exact superpose eq6933 eq25
    | exact resolve eq25 eq6933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6947 : x ≠ y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  have eq6994 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6937
       have i₂ := eq6933
       grind)
    | exact superpose eq6933 eq6937
    | exact resolve eq6937 eq6933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6933 eq6937
  have eq7009 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6994
  have eq7012 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7009
       have r₂ := eq6947
       grind)
    | exact resolve eq7009 eq6947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6947 eq7009
  have eq8064 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5118 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5118
    | exact resolve eq5118 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5118
  have eq8180 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8064 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8064
    | (have j0 := eq8064 X0 X1
       grind)
    | exact resolve eq8064 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8064
  have eq35148 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4695
       have i₂ := eq7012
       grind)
    | exact superpose eq7012 eq4695
    | exact resolve eq4695 eq7012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4695 eq7012
  have eq35154 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq35148
  have eq35155 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq35154
  have eq35163 : y = (τ (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq35155
       grind)
    | exact superpose eq35155 eq10
    | exact resolve eq10 eq35155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35155
  have eq35265 : x = y ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq35163
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35163
    | exact resolve eq35163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35163
  have eq35589 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35265
       grind)
    | exact superpose eq35265 eq16
    | exact resolve eq16 eq35265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35265
  have eq35590 : (σ x) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq35589
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq35589
    | exact resolve eq35589 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35589
  have eq35591 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq35590
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq35590
    | exact resolve eq35590 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35590
  have eq35592 : (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq35591
  have eq35620 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq35592
       grind)
    | exact superpose eq35592 eq11
    | exact resolve eq11 eq35592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35592
  have eq36026 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35620
       grind)
    | exact superpose eq35620 eq16
    | exact resolve eq16 eq35620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36054 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq25 (σ x) (σ y)
       have i₂ := eq35620
       grind)
    | exact superpose eq35620 eq25
    | exact resolve eq25 eq35620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq36163 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq36026
       have i₂ := eq8180 x y
       grind)
    | exact superpose eq8180 eq36026
    | (have j1 := eq8180 x y
       grind)
    | (have r₁ := eq36026
       have r₂ := eq8180 x y
       grind)
    | (have r₁ := eq36026
       have r₂ := eq8180 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq36026
       have r₂ := eq8180 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq36026 eq8180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8180
  have eq36164 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq36026
       have i₂ := eq774 y x
       grind)
    | exact superpose eq774 eq36026
    | (have j1 := eq774 y x
       grind)
    | (have r₁ := eq36026
       have r₂ := eq774 y x
       grind)
    | (have r₁ := eq36026
       have r₂ := eq774 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq36026
       have r₂ := eq774 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq36026 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq36165 : x = y ∨ x = (M.op x y) := by grind
  clear eq36164
  have eq36166 : x = y ∨ y = (k x y) := by grind
  clear eq36163
  have eq36464 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36026
       have i₂ := eq36165
       grind)
    | exact superpose eq36165 eq36026
    | exact resolve eq36026 eq36165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36165
  have eq36465 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36464
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq36464
    | exact resolve eq36464 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36464
  have eq36469 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36465
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq36465
    | exact resolve eq36465 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36465
  have eq36470 : x = (M.op x y) := by grind
  clear eq36469
  have eq36859 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq36026
       have i₂ := eq36166
       grind)
    | exact superpose eq36166 eq36026
    | exact resolve eq36026 eq36166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36166
  have eq36863 : (σ x) ≠ (σ (M.op x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq36859
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq36859
    | exact resolve eq36859 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq36859
  have eq36867 : (σ x) ≠ (σ x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq36863
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq36863
    | exact resolve eq36863 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq36863
  have eq36868 : y = (k x y) := by grind
  clear eq36867
  have eq37153 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq36026
       have i₂ := eq36868
       grind)
    | exact superpose eq36868 eq36026
    | exact resolve eq36026 eq36868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36026
  have eq37194 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq37153
       have i₂ := eq36470
       grind)
    | exact superpose eq36470 eq37153
    | exact resolve eq37153 eq36470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36470 eq37153
  have eq37902 : (σ x) = (M.op (σ x) (σ (k x (k x y)))) ∨ (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq36054
       have i₂ := eq96 x (k x y)
       grind)
    | exact superpose eq96 eq36054
    | (have j1 := eq96 x (k x y)
       grind)
    | exact resolve eq36054 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq36054
  have eq37958 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq37902
       have i₂ := eq36868
       grind)
    | exact superpose eq36868 eq37902
    | exact resolve eq37902 eq36868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37902
  have eq37959 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq37958
  have eq37972 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq37959
       have i₂ := eq36868
       grind)
    | exact superpose eq36868 eq37959
    | exact resolve eq37959 eq36868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37959
  have eq37982 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq37972
       have i₂ := eq35620
       grind)
    | exact superpose eq35620 eq37972
    | exact resolve eq37972 eq35620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35620 eq37972
  have eq37983 : (σ x) = (σ (k x y)) := by grind
  clear eq37982
  have eq37990 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq37983
       have i₂ := eq36868
       grind)
    | exact superpose eq36868 eq37983
    | exact resolve eq37983 eq36868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36868 eq37983
  have eq37995 : False := by grind
  exact eq37995
