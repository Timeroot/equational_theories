import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pyx_pxx_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
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
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq96 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq43 X1
       grind)
    | exact superpose eq43 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq98 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq96
    | (have j0 := eq96 X0 X1
       grind)
    | exact resolve eq96 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq96
  have eq409 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
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
  have eq458 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq409
    | (have j0 := eq409 X0 X1
       grind)
    | exact resolve eq409 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq409
  have eq464 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq458 X0 X1
       have j1 := eq84 X1 X0
       grind)
    | (have r₁ := eq458 X1 (τ X1)
       have r₂ := eq84 (τ X1) X1
       grind)
    | (have r₁ := eq458 X1 X0
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq458 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq458
  have eq468 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq464
    | (have j0 := eq464 X0 X1
       grind)
    | exact resolve eq464 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq464
  have eq1060 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq468 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq468
    | exact resolve eq468 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq1166 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq1060 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq1060 X0 X1
       grind)
    | exact superpose eq1060 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq1060 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq1060 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq1060 X1 X1
       grind)
    | exact resolve eq12 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1167 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq1060 X0 X1
       grind)
    | (have i₁ := eq13 X1 X0
       have i₂ := eq1060 X0 X1
       grind)
    | exact superpose eq1060 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq1060 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq1060 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq1060 X0 X1
       grind)
    | exact resolve eq13 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1202 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1167 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1224 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1166 X0 X1
       have j1 := eq1202 X0 X1
       grind)
    | (have r₁ := eq1166 X0 X1
       have r₂ := eq1202 X0 X1
       grind)
    | (have r₁ := eq1166 X1 X0
       have r₂ := eq1202 X0 X1
       grind)
    | exact resolve eq1166 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166 eq1202
  have eq1377 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1383 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1377 X0 X1
       have j1 := eq1060 X1 X0
       grind)
    | (have r₁ := eq1377 X0 X0
       have r₂ := eq1060 X0 X0
       grind)
    | (have r₁ := eq1377 X1 X0
       have r₂ := eq1060 X0 X1
       grind)
    | exact resolve eq1377 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060 eq1377
  have eq1507 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1383 (σ X1) (σ X0)
       grind)
    | exact superpose eq1383 eq15
    | exact resolve eq15 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1526 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1507 X0 X1
       have i₂ := eq1383 X1 X0
       grind)
    | exact superpose eq1383 eq1507
    | exact resolve eq1507 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383 eq1507
  have eq1951 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1526 x y
       grind)
    | exact superpose eq1526 eq16
    | (have r₁ := eq16
       have r₂ := eq1526 x y
       grind)
    | exact resolve eq16 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1992 : False := by grind
  exact eq1992

/-- `Equation1489`: `x = (y ◇ x) ◇ (y ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation1489 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1489 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1489.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq81 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq96 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq108 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq96 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq96 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq115 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq108 (σ X0) (σ X1)
       grind)
    | exact superpose eq108 eq15
    | exact resolve eq15 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq115 X0 X1
       have i₂ := eq108 X0 X1
       grind)
    | exact superpose eq108 eq115
    | exact resolve eq115 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq115
  have eq275 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq124 x y
       grind)
    | exact superpose eq124 eq16
    | (have r₁ := eq16
       have r₂ := eq124 x y
       grind)
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq285 : False := by grind
  exact eq285

/-- `Equation1491`: `x = (y ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyy_x_pyx_Equation1491 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1491 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1491.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X1 X0))) = X0 := by
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
  have eq29 : x = (τ (σ x)) := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq44 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44
    | (have j0 := eq44 y
       grind)
    | exact resolve eq44 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : y = (M.op (M.op x y) (M.op x (M.op x y))) := by
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
  have eq175 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 (M.op X1 X0)) (M.op X1 X0)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (σ (M.op x x)) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq39 (M.op x x)
       have i₂ := eq177 x
       grind)
    | exact superpose eq177 eq39
    | exact resolve eq39 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq41 (M.op sF0 sF0)
       have i₂ := eq177 sF0
       grind)
    | exact superpose eq177 eq41
    | exact resolve eq41 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq215 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq177 sF2
       grind)
    | exact superpose eq177 eq141
    | exact resolve eq141 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : (τ (M.op (σ y) (σ y))) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | (have i₁ := eq152 (M.op sF3 sF3)
       have i₂ := eq177 sF3
       grind)
    | exact superpose eq177 eq152
    | exact resolve eq152 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq752 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
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
  have eq755 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 X1 : G, (M.op (k X0 X1) (M.op X1 (k X0 X1))) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq762
       grind)
    | exact superpose eq762 eq39
    | exact resolve eq39 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq830
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq830
    | exact resolve eq830 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq833 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq831
    | exact resolve eq831 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq833 eq765
    | exact resolve eq765 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq841
       have r₂ := eq27
       grind)
    | exact resolve eq841 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq853 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq848 eq215
    | exact resolve eq215 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq848 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq857 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq848 eq176
    | exact resolve eq176 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq858 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq848 eq16
    | exact resolve eq16 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq860 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ y) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq848 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq848
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq848
       grind)
    | exact resolve eq13 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq861 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq854
  have eq863 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq858
    | exact resolve eq858 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq864 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq857
    | exact resolve eq857 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq865 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq860 (σ x)
       grind)
    | (have r₁ := eq861
       have r₂ := eq860 (k (σ x) (σ x))
       grind)
    | (have r₁ := eq861
       have r₂ := eq860 (σ x)
       grind)
    | exact resolve eq861 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq861
  have eq866 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq853
    | exact resolve eq853 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq867 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq866
       have r₂ := eq752
       grind)
    | exact resolve eq866 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752 eq866
  have eq869 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq762
       have i₂ := eq867
       grind)
    | exact superpose eq867 eq762
    | exact resolve eq762 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq871 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq867
       grind)
    | exact superpose eq867 eq39
    | exact resolve eq39 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq869
  have eq874 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq871
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq871
    | exact resolve eq871 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq879 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq874 eq833
    | exact resolve eq833 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq885 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq879
  have eq894 : y = (k x x) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq872
       grind)
    | exact superpose eq872 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq897 : (M.op x y) = (M.op x (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq176 x x
       have i₂ := eq872
       grind)
    | exact superpose eq872 eq176
    | exact resolve eq176 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16 x x
       have i₂ := eq872
       grind)
    | exact superpose eq872 eq16
    | exact resolve eq16 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : ∀ X0 : G, y ≠ X0 ∨ y = (k X0 x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq872
       grind)
    | exact superpose eq872 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq872
       grind)
    | exact resolve eq13 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq894
  have eq903 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq898
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq898
    | exact resolve eq898 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq904 : (M.op x y) = (M.op x (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq897
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq897
    | exact resolve eq897 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq905 : y = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq900 x
       grind)
    | (have r₁ := eq901
       have r₂ := eq900 (k x x)
       grind)
    | (have r₁ := eq901
       have r₂ := eq900 x
       grind)
    | (have r₁ := eq901
       have r₂ := eq900 (M.op x y)
       grind)
    | exact resolve eq901 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900 eq901
  have eq935 : (M.op (M.op x y) (M.op x (M.op x y))) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq903 eq176
    | exact resolve eq176 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq937 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq174 eq935
    | exact resolve eq935 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq1005 : (M.op y y) = (M.op x (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq176 x y
       have i₂ := eq937
       grind)
    | exact superpose eq937 eq176
    | exact resolve eq176 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq1008 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq904 eq1005
    | exact resolve eq1005 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904 eq1005
  have eq1036 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq1008
       grind)
    | exact superpose eq1008 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1044 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1036
  have eq1074 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1044
       grind)
    | exact superpose eq1044 eq40
    | exact resolve eq40 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1076 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1074
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1074
    | exact resolve eq1074 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1078 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1076
    | exact resolve eq1076 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1347 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq863 eq176
    | exact resolve eq176 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq1349 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq175 eq1347
    | exact resolve eq1347 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347
  have eq1352 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq865 eq97
    | exact resolve eq97 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq1363 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq1352
    | exact resolve eq1352 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq1366 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq905 eq1363
    | exact resolve eq1363 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq1372 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1349 eq176
    | exact resolve eq176 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1375 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq864 eq1372
    | exact resolve eq1372 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq1372
  have eq1386 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq16 x x
       have i₂ := eq1366
       grind)
    | exact superpose eq1366 eq16
    | exact resolve eq16 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366
  have eq1396 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq174 eq1386
    | exact resolve eq1386 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1399 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq905 eq1396
    | exact resolve eq1396 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq1396
  have eq1400 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1399
  have eq1427 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1375 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1433 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1375 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq1375
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1375
       grind)
    | exact resolve eq13 eq1375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1434 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1427
  have eq1439 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq1433 (σ y)
       grind)
    | (have r₁ := eq1434
       have r₂ := eq1433 (k (σ y) (σ y))
       grind)
    | (have r₁ := eq1434
       have r₂ := eq1433 (σ y)
       grind)
    | (have r₁ := eq1434
       have r₂ := eq1433 (σ x)
       grind)
    | exact resolve eq1434 eq1433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433 eq1434
  have eq1450 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq771 x x
       have i₂ := eq1400
       grind)
    | exact superpose eq1400 eq771
    | (have j0 := eq771 x x
       grind)
    | exact resolve eq771 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1457 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq771 y x
       have i₂ := eq867
       grind)
    | exact superpose eq867 eq771
    | (have j0 := eq771 y x
       grind)
    | exact resolve eq771 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq1500 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1457
  have eq1503 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1450
  have eq1523 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1500
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1500
    | exact resolve eq1500 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500
  have eq1526 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1503
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1503
    | exact resolve eq1503 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq1543 : x = (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1523
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1523
    | exact resolve eq1523 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1553 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq872 eq1543
    | exact resolve eq1543 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq1543
  have eq1632 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1553 eq182
    | exact resolve eq182 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq1646 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1632
    | exact resolve eq1632 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq1648 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq885 eq1646
    | exact resolve eq1646 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq2051 : (M.op x y) = (M.op x (M.op y x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1526 eq16
    | exact resolve eq16 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2052 : (M.op (M.op x y) (M.op x (M.op x y))) = (M.op y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1526 eq176
    | exact resolve eq176 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq2059 : y = (M.op y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq174 eq2052
    | exact resolve eq2052 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2185 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1648 eq1439
    | exact resolve eq1439 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439 eq1648
  have eq2199 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2185
  have eq2211 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180
       have i₂ := eq2199
       grind)
    | exact superpose eq2199 eq180
    | exact resolve eq180 eq2199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq2229 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2211
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2211
    | exact resolve eq2211 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211
  have eq2275 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2229 eq765
    | exact resolve eq765 eq2229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765 eq2229
  have eq2282 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2275
  have eq2309 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2282 eq16
    | exact resolve eq16 eq2282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2310 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2282 eq176
    | exact resolve eq176 eq2282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282
  have eq2318 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2310
    | exact resolve eq2310 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310
  have eq2319 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2309
    | exact resolve eq2309 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309
  have eq2350 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2319 eq176
    | exact resolve eq176 eq2319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319
  have eq2358 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq175 eq2350
    | exact resolve eq2350 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq2415 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2358 eq176
    | exact resolve eq176 eq2358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358
  have eq2420 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2318 eq2415
    | exact resolve eq2415 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318 eq2415
  have eq2439 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2420 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq2420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420
  have eq2448 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2439
  have eq2486 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2448 eq1078
    | exact resolve eq1078 eq2448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078 eq2448
  have eq2496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2486
  have eq2503 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2496
       have r₂ := eq27
       grind)
    | exact resolve eq2496 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2496
  have eq2506 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2503 eq175
    | exact resolve eq175 eq2503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2520 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2506
    | exact resolve eq2506 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2506
  have eq2522 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2503 eq2520
    | exact resolve eq2520 eq2503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2520
  have eq2678 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2522 eq236
    | exact resolve eq236 eq2522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522
  have eq2691 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq2678
    | exact resolve eq2678 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2678
  have eq2692 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1044 eq2691
    | exact resolve eq2691 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq2691
  have eq2693 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2692
  have eq2696 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2693 eq175
    | exact resolve eq175 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2697 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2693 eq179
    | exact resolve eq179 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2701 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2697
    | exact resolve eq2697 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697
  have eq2702 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2693 eq2701
    | exact resolve eq2701 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2701
  have eq2709 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2696 eq176
    | exact resolve eq176 eq2696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2720 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2709
    | exact resolve eq2709 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2709
  have eq2724 : (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2693 eq2720
    | exact resolve eq2720 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720
  have eq2738 : (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ x))) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2702 eq176
    | exact resolve eq176 eq2702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702
  have eq2748 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2738
       have i₂ := eq176 sF2 sF2
       grind)
    | exact superpose eq176 eq2738
    | exact resolve eq2738 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2738
  have eq2751 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2696 eq2748
    | exact resolve eq2748 eq2696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2696 eq2748
  have eq2786 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2751 eq176
    | exact resolve eq176 eq2751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2751
  have eq2794 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2724 eq2786
    | exact resolve eq2786 eq2724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724 eq2786
  have eq2836 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2794 eq236
    | exact resolve eq236 eq2794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq2839 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2794 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq2794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2794
  have eq2846 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2839
  have eq2857 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2836
    | exact resolve eq2836 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2836
  have eq2951 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2846 eq115
    | exact resolve eq115 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846
  have eq2979 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2951
    | exact resolve eq2951 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951
  have eq3303 : x = (M.op y (M.op y y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq2059
       grind)
    | exact superpose eq2059 eq16
    | exact resolve eq16 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3304 : (M.op y y) = (M.op x (M.op y x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq176 x y
       have i₂ := eq2059
       grind)
    | exact superpose eq2059 eq176
    | exact resolve eq176 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq3313 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2051 eq3304
    | exact resolve eq3304 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051 eq3304
  have eq3314 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2693 eq3303
    | exact resolve eq3303 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3303
  have eq3317 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2693 eq3313
    | exact resolve eq3313 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3313
  have eq3441 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3317 eq176
    | exact resolve eq176 eq3317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3453 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3314 eq3441
    | exact resolve eq3441 eq3314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3314 eq3441
  have eq3458 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3317 eq3453
    | exact resolve eq3453 eq3317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317 eq3453
  have eq3459 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3458
  have eq3471 : x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq885
       have i₂ := eq3459
       grind)
    | exact superpose eq3459 eq885
    | exact resolve eq885 eq3459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq3474 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2199
       have i₂ := eq3459
       grind)
    | exact superpose eq3459 eq2199
    | exact resolve eq2199 eq3459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199 eq3459
  have eq3480 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3474
  have eq3483 : x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3471
  have eq3494 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2503 eq3480
    | exact resolve eq3480 eq2503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503 eq3480
  have eq3495 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3494
  have eq3498 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2693 eq3483
    | exact resolve eq3483 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2693 eq3483
  have eq3499 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3498
  have eq3512 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3495 eq27
    | exact resolve eq27 eq3495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3495
  have eq3541 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3512
       have r₂ := eq3499
       grind)
    | exact resolve eq3512 eq3499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3499 eq3512
  have eq3549 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3541 eq27
    | exact resolve eq27 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3550 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3541 eq175
    | exact resolve eq175 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq3551 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3541 eq179
    | exact resolve eq179 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq3552 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3541 eq755
    | (have r₁ := eq755
       have r₂ := eq3541
       grind)
    | exact resolve eq755 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq3553 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3552
  have eq3556 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3551
    | exact resolve eq3551 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3551
  have eq3557 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3541 eq3556
    | exact resolve eq3556 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3556
  have eq3575 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3550 eq176
    | exact resolve eq176 eq3550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3586 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3575
    | exact resolve eq3575 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3575
  have eq3590 : (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3541 eq3586
    | exact resolve eq3586 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3541 eq3586
  have eq3608 : (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ x))) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3557 eq176
    | exact resolve eq176 eq3557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3557
  have eq3620 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3608
       have i₂ := eq176 sF2 sF2
       grind)
    | exact superpose eq176 eq3608
    | exact resolve eq3608 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3608
  have eq3623 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3550 eq3620
    | exact resolve eq3620 eq3550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3550 eq3620
  have eq3658 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3623 eq176
    | exact resolve eq176 eq3623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3623
  have eq3666 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3590 eq3658
    | exact resolve eq3658 eq3590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3590 eq3658
  have eq3680 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3666 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq3666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666
  have eq3687 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3680
  have eq4018 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3553 eq141
    | exact resolve eq141 eq3553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq3553
  have eq4029 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq4018
    | exact resolve eq4018 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4018
  have eq4035 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4029 eq215
    | exact resolve eq215 eq4029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq4029
  have eq4088 : y = (k y x) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq4035
    | exact resolve eq4035 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4035
  have eq4089 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq4088
  have eq4098 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq762
       have i₂ := eq4089
       grind)
    | exact superpose eq4089 eq762
    | exact resolve eq762 eq4089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq4100 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq4089
       grind)
    | exact superpose eq4089 eq39
    | exact resolve eq39 eq4089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq4089
  have eq4103 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq4098
  have eq4108 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4100
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4100
    | exact resolve eq4100 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4100
  have eq4119 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4108 eq833
    | exact resolve eq833 eq4108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq4108
  have eq4124 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4119
  have eq4143 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16 x x
       have i₂ := eq4103
       grind)
    | exact superpose eq4103 eq16
    | exact resolve eq16 eq4103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4144 : (M.op x y) = (M.op x (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq176 x x
       have i₂ := eq4103
       grind)
    | exact superpose eq4103 eq176
    | exact resolve eq176 eq4103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4103
  have eq4156 : (M.op x y) = (M.op x (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4144
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4144
    | exact resolve eq4144 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144
  have eq4157 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4143
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4143
    | exact resolve eq4143 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4143
  have eq4189 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq16 x x
       have i₂ := eq4124
       grind)
    | exact superpose eq4124 eq16
    | exact resolve eq16 eq4124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4190 : (M.op x y) = (M.op x (M.op y x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq176 x x
       have i₂ := eq4124
       grind)
    | exact superpose eq4124 eq176
    | exact resolve eq176 eq4124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4124
  have eq4202 : (M.op x y) = (M.op x (M.op y x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq4190
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4190
    | exact resolve eq4190 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4190
  have eq4203 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq4189
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4189
    | exact resolve eq4189 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4189
  have eq4211 : (M.op (M.op x y) (M.op x (M.op x y))) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4157 eq176
    | exact resolve eq176 eq4157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4157
  have eq4220 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq174 eq4211
    | exact resolve eq4211 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4211
  have eq4228 : (M.op (M.op x y) (M.op x (M.op x y))) = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4203 eq176
    | exact resolve eq176 eq4203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4237 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq174 eq4228
    | exact resolve eq4228 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228
  have eq4247 : (M.op y y) = (M.op x (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq176 x y
       have i₂ := eq4220
       grind)
    | exact superpose eq4220 eq176
    | exact resolve eq176 eq4220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4220
  have eq4255 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4156 eq4247
    | exact resolve eq4247 eq4156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4156 eq4247
  have eq4262 : (M.op y y) = (M.op x (M.op y x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq176 x y
       have i₂ := eq4237
       grind)
    | exact superpose eq4237 eq176
    | exact resolve eq176 eq4237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4237
  have eq4270 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4202 eq4262
    | exact resolve eq4262 eq4202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4202 eq4262
  have eq4276 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq4255
       grind)
    | exact superpose eq4255 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4255
  have eq4285 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4276
  have eq4332 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2979
       have i₂ := eq4285
       grind)
    | exact superpose eq4285 eq2979
    | exact resolve eq2979 eq4285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2979
  have eq4341 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq4332
  have eq4361 : (k x y) = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4341 eq98
    | exact resolve eq98 eq4341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq4364 : (k y y) = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4341 eq115
    | exact resolve eq115 eq4341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4341
  have eq4487 : (k x x) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq97 eq4364
    | exact resolve eq4364 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4364
  have eq4490 : (k x x) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq97 eq4361
    | exact resolve eq4361 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq4361
  have eq4504 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4285 eq4487
    | exact resolve eq4487 eq4285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4285 eq4487
  have eq4506 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2857 eq4490
    | exact resolve eq4490 eq2857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857 eq4490
  have eq4509 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4504 eq4506
    | exact resolve eq4506 eq4504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4504 eq4506
  have eq4510 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4509
  have eq4513 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4510
       grind)
    | exact superpose eq4510 eq18
    | exact resolve eq18 eq4510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4551 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4203
       have i₂ := eq4510
       grind)
    | exact superpose eq4510 eq4203
    | exact resolve eq4203 eq4510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4203
  have eq4553 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4270
       have i₂ := eq4510
       grind)
    | exact superpose eq4510 eq4270
    | exact resolve eq4270 eq4510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4270
  have eq4554 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4553
  have eq4556 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4551
  have eq4587 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4554 eq4556
    | exact resolve eq4556 eq4554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4554 eq4556
  have eq4588 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq4587
  have eq4620 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4588 eq3549
    | exact resolve eq3549 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3549
  have eq4621 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq4620
  have eq4664 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4513 eq174
    | exact resolve eq174 eq4513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4513
  have eq4687 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4510 eq4664
    | exact resolve eq4664 eq4510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4510 eq4664
  have eq4720 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4687 eq182
    | exact resolve eq182 eq4687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq4687
  have eq4742 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4720
    | exact resolve eq4720 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4720
  have eq4744 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4588 eq4742
    | exact resolve eq4742 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4588 eq4742
  have eq4786 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4744 eq3687
    | exact resolve eq3687 eq4744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3687 eq4744
  have eq4797 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq4786
  have eq4814 : x = (M.op x y) := by
    first
    | (have r₁ := eq4797
       have r₂ := eq4621
       grind)
    | exact resolve eq4797 eq4621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4621 eq4797
  have eq4905 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4814
       grind)
    | exact superpose eq4814 eq18
    | exact resolve eq18 eq4814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4906 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4814
       grind)
    | exact superpose eq4814 eq22
    | exact resolve eq22 eq4814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4909 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq174
       have i₂ := eq4814
       grind)
    | exact superpose eq4814 eq174
    | exact resolve eq174 eq4814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq4916 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4906 eq20
    | exact resolve eq20 eq4906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4906
  have eq5064 : (M.op y (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4905 eq176
    | exact resolve eq176 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5070 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq4905 eq5064
    | exact resolve eq5064 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5064
  have eq5082 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op y (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq4909 eq176
    | exact resolve eq176 eq4909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5090 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op y (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq4905 eq5082
    | exact resolve eq5082 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4905 eq5082
  have eq5112 : (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq5070 eq176
    | exact resolve eq176 eq5070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5070
  have eq5118 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq5112
       have i₂ := eq176 sF0 sF0
       grind)
    | exact superpose eq176 eq5112
    | exact resolve eq5112 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5112
  have eq5121 : y = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq4909 eq5118
    | exact resolve eq5118 eq4909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4909 eq5118
  have eq5160 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op y (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq5121 eq176
    | exact resolve eq176 eq5121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5121
  have eq5166 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq5090 eq5160
    | exact resolve eq5160 eq5090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5090 eq5160
  have eq5172 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq5166
       grind)
    | exact superpose eq5166 eq13
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq5166
       grind)
    | exact resolve eq13 eq5166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5173 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq5166
       grind)
    | exact superpose eq5166 eq11
    | exact resolve eq11 eq5166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5166
  have eq5180 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq5173
  have eq5222 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq5180
       grind)
    | exact superpose eq5180 eq40
    | exact resolve eq40 eq5180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5180
  have eq5234 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5222
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5222
    | exact resolve eq5222 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5222
  have eq5236 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq5234
    | exact resolve eq5234 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5234
  have eq5238 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4916 eq5236
    | exact resolve eq5236 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5236
  have eq5247 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5238 eq115
    | exact resolve eq115 eq5238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq5238
  have eq5273 : x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq5247
    | exact resolve eq5247 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5247
  have eq5276 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5273
       have i₂ := eq4814
       grind)
    | exact superpose eq4814 eq5273
    | exact resolve eq5273 eq4814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4814 eq5273
  have eq5279 : (M.op x y) = (k y y) := by
    first
    | (have j1 := eq5172 y
       grind)
    | (have r₁ := eq5276
       have r₂ := eq5172 (k y y)
       grind)
    | (have r₁ := eq5276
       have r₂ := eq5172 y
       grind)
    | exact resolve eq5276 eq5172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5172 eq5276
  have eq5290 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq5279
       grind)
    | exact superpose eq5279 eq40
    | exact resolve eq40 eq5279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5279
  have eq5304 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq5290
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5290
    | exact resolve eq5290 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5290
  have eq5306 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq5304
    | exact resolve eq5304 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5304
  have eq5308 : (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq4916 eq5306
    | exact resolve eq5306 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5306
  have eq5328 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq5308 eq771
    | (have j0 := eq771 (σ y) (σ y)
       grind)
    | exact resolve eq771 eq5308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq5329 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq5308 eq798
    | (have j0 := eq798 (σ y) (σ y)
       grind)
    | exact resolve eq798 eq5308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq5330 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5329
  have eq5331 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5328
  have eq7419 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ y) (σ x)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq5331 eq176
    | exact resolve eq176 eq5331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq5331
  have eq7427 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7419
       have i₂ := eq16 sF2 sF3
       grind)
    | exact superpose eq16 eq7419
    | exact resolve eq7419 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7419
  have eq7436 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq7427
    | exact resolve eq7427 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7427
  have eq7453 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7436 eq177
    | exact resolve eq177 eq7436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq7436
  have eq7466 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5308 eq7453
    | exact resolve eq7453 eq5308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5308 eq7453
  have eq7472 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7466 eq27
    | exact resolve eq27 eq7466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7466
  have eq7480 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq7472
       have r₂ := eq4916
       grind)
    | exact resolve eq7472 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7472
  have eq7482 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7480 eq26
    | exact resolve eq26 eq7480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq7560 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7480 eq5330
    | (have r₁ := eq5330
       have r₂ := eq7480
       grind)
    | exact resolve eq5330 eq7480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5330 eq7480
  have eq7567 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7560
  have eq7605 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7567 eq7482
    | exact resolve eq7482 eq7567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7482 eq7567
  have eq7637 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq7605 eq27
    | exact resolve eq27 eq7605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq7605
  have eq7645 : False := by grind
  exact eq7645

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxy_x_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  clear eq43
  have eq50 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op x X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq49
    | exact resolve eq49 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq73
    | exact resolve eq73 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq71
    | exact resolve eq71 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq101 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq101
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq250 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op (σ y) X0)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X1 : G, (M.op (σ y) (M.op X1 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X0)
       have i₂ := eq56 X0 X2
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq69 (τ X0)
       grind)
    | exact superpose eq69 eq34
    | exact resolve eq34 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq385 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq374 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq374
    | exact resolve eq374 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq387 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq385 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq385
    | exact resolve eq385 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq385
  have eq521 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (σ X0) (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq56
    | exact resolve eq56 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq662 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 X1) X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X2 (M.op X0 (M.op (M.op X2 X1) X0))
       have i₂ := eq14 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X0 (M.op (M.op y (M.op X1 y)) X0))
       have i₂ := eq52 y X1 X0
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op x (M.op (M.op sF3 (M.op x sF3)) x))
       have i₂ := eq52 sF3 x x
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq690 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq16
    | exact resolve eq16 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq821 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0) (τ X0)
       have i₂ := eq690 X0
       grind)
    | exact superpose eq690 eq56
    | exact resolve eq56 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq847 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X0 (M.op (M.op x y) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op (M.op (M.op y (M.op x y)) y) (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq857 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X1 X2 (M.op X1 X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq908 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq262 sF4
       have i₂ := eq56 sF4 sF3
       grind)
    | exact superpose eq56 eq262
    | exact resolve eq262 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq1551 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0))
       have i₂ := eq274 X0 x x
       grind)
    | exact superpose eq274 eq56
    | exact resolve eq56 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1554 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1551 X0
       have i₂ := eq274 X0 X0 X0
       grind)
    | exact superpose eq274 eq1551
    | exact resolve eq1551 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq3893 : (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) = (M.op y (M.op (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq847 (M.op sF0 (M.op sF0 sF0))
       have i₂ := eq1554 sF0
       grind)
    | exact superpose eq1554 eq847
    | exact resolve eq847 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3918 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq3893
       have i₂ := eq14 sF0 (M.op sF0 (M.op sF0 sF0)) sF0
       grind)
    | exact superpose eq14 eq3893
    | exact resolve eq3893 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893
  have eq3920 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq3918 eq847
    | exact resolve eq847 eq3918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847 eq3918
  have eq3943 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3920 eq14
    | exact resolve eq14 eq3920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3976 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq848 (M.op sF4 (M.op sF4 sF4))
       have i₂ := eq1554 sF4
       grind)
    | exact superpose eq1554 eq848
    | exact resolve eq848 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4001 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3976
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3976
    | exact resolve eq3976 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3976
  have eq4020 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4001 eq848
    | exact resolve eq848 eq4001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4105 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3943 eq50
    | exact resolve eq50 eq3943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq3943
  have eq4137 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq4105 eq3920
    | exact resolve eq3920 eq4105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920 eq4105
  have eq4282 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq908 eq250
    | exact resolve eq250 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq4316 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq4282 X0
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq4282
    | exact resolve eq4282 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4282
  have eq4317 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4316 x
       have i₂ := eq56 sF4 x
       grind)
    | exact superpose eq56 eq4316
    | exact resolve eq4316 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4316
  have eq4318 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4001 eq4317
    | exact resolve eq4317 eq4001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4001 eq4317
  have eq4319 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4318 eq4020
    | exact resolve eq4020 eq4318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4020
  have eq5393 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X2 X0) (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq662 (M.op X0 (M.op X0 X0)) (M.op X2 X0) x
       have i₂ := eq274 X0 x X2
       grind)
    | exact superpose eq274 eq662
    | exact resolve eq662 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq5490 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq5393 X0 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq14 eq5393
    | exact resolve eq5393 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5393
  have eq5500 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq5490 X0 x
       have i₂ := eq56 X0 x
       grind)
    | exact superpose eq56 eq5490
    | exact resolve eq5490 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5490
  have eq6737 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq821 (M.op X0 (M.op X0 X0))
       have i₂ := eq274 X0 X0 X0
       grind)
    | exact superpose eq274 eq821
    | exact resolve eq821 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7009 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq857 X0 X1 X2 X3
       have i₂ := eq5500 X0
       grind)
    | exact superpose eq5500 eq857
    | exact resolve eq857 eq5500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq7020 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7009 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0)) X1 X2
       have i₂ := eq274 X0 x x
       grind)
    | exact superpose eq274 eq7009
    | exact resolve eq7009 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7009
  have eq7241 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7020 X0 X1 X2
       have i₂ := eq274 X0 X0 X0
       grind)
    | exact superpose eq274 eq7020
    | exact resolve eq7020 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7020
  have eq7276 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7241 X0 X1 X2
       have i₂ := eq5500 X0
       grind)
    | exact superpose eq5500 eq7241
    | exact resolve eq7241 eq5500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5500 eq7241
  have eq7335 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq7276 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7276
    | (have j0 := eq7276 y X0 x
       grind)
    | exact resolve eq7276 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7347 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq7276
    | (have j0 := eq7276 (σ y) X0 (σ x)
       grind)
    | exact resolve eq7276 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7425 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq848 X0
       have i₂ := eq7276 X0 X0 sF4
       grind)
    | exact superpose eq7276 eq848
    | exact resolve eq848 eq7276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq8851 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq671 X0 X1
       have i₂ := eq7276 X0 X0 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq7276 eq671
    | exact resolve eq671 eq7276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq8881 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 y x X0
       have i₂ := eq8851 X0 x
       grind)
    | exact superpose eq8851 eq52
    | exact resolve eq52 eq8851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8851
  have eq9015 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq8881 (M.op X0 (M.op X0 X0))
       have i₂ := eq274 X0 X0 X0
       grind)
    | exact superpose eq274 eq8881
    | exact resolve eq8881 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9139 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1554 X0
       have i₂ := eq9015 X0
       grind)
    | exact superpose eq9015 eq1554
    | exact resolve eq1554 eq9015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq9145 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq9015 X0
       grind)
    | exact superpose eq9015 eq14
    | exact resolve eq14 eq9015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9159 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq7425 sF4
       have i₂ := eq9015 sF4
       grind)
    | exact superpose eq9015 eq7425
    | exact resolve eq7425 eq9015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7425
  have eq9207 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq908
       have i₂ := eq9015 sF4
       grind)
    | exact superpose eq9015 eq908
    | exact resolve eq908 eq9015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq9227 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq9015 eq14
    | exact resolve eq14 eq9015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9252 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9227 X0 X1
       have i₂ := eq14 X0 sF0 X0
       grind)
    | exact superpose eq14 eq9227
    | exact resolve eq9227 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9227
  have eq9287 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4318 eq9159
    | exact resolve eq9159 eq4318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4318 eq9159
  have eq9361 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq672 X0 X1
       have i₂ := eq7276 X0 X0 (M.op sF3 (M.op X1 sF3))
       grind)
    | exact superpose eq7276 eq672
    | exact resolve eq672 eq7276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq7276
  have eq9632 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq9361 eq52
    | exact resolve eq52 eq9361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9361
  have eq9780 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq9632 (M.op X0 (M.op X0 X0))
       have i₂ := eq274 X0 X0 X0
       grind)
    | exact superpose eq274 eq9632
    | exact resolve eq9632 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq9632
  have eq10076 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op (M.op x y) (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq855 X0 X1 X2
       have i₂ := eq9252 (M.op y sF0) (M.op y sF0)
       grind)
    | exact superpose eq9252 eq855
    | exact resolve eq855 eq9252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq9252
  have eq10077 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op y (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4137 eq10076
    | exact resolve eq10076 eq4137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10076
  have eq10078 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op y (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq7335 eq10077
    | exact resolve eq10077 eq7335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7335 eq10077
  have eq10337 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq9780 eq14
    | exact resolve eq14 eq9780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9780
  have eq10362 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10337 X0 X1
       have i₂ := eq14 X0 sF4 X0
       grind)
    | exact superpose eq14 eq10337
    | exact resolve eq10337 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10337
  have eq10490 : (M.op y y) = (M.op x (M.op y (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq10078 (M.op x (M.op x x)) x x
       have i₂ := eq52 x x x
       grind)
    | exact superpose eq52 eq10078
    | exact resolve eq10078 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10078
  have eq10992 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq10362 eq856
    | exact resolve eq856 eq10362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856 eq10362
  have eq10993 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4319 eq10992
    | exact resolve eq10992 eq4319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4319 eq10992
  have eq10994 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq7347 eq10993
    | exact resolve eq10993 eq7347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7347 eq10993
  have eq11022 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq10994 (M.op x (M.op x x)) x sF2
       have i₂ := eq52 x x sF2
       grind)
    | exact superpose eq52 eq10994
    | exact resolve eq10994 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq10994
  have eq12432 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq9287 eq11022
    | exact resolve eq11022 eq9287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9287 eq11022
  have eq20463 : (M.op x y) = (M.op (M.op x y) (τ (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))))) := by
    first
    | exact superpose eq30 eq6737
    | exact resolve eq6737 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq20464 : x = (M.op x (τ (M.op (σ x) (M.op (σ x) (σ x))))) := by
    first
    | exact superpose eq28 eq6737
    | exact resolve eq6737 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6737
  have eq20558 : x = (M.op x (τ (M.op y (M.op (M.op x y) (σ x))))) := by
    first
    | (have i₁ := eq20464
       have i₂ := eq9015 sF2
       grind)
    | exact superpose eq9015 eq20464
    | exact resolve eq20464 eq9015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20464
  have eq20559 : (M.op x y) = (M.op (M.op x y) (τ (M.op y (M.op (M.op x y) (σ (M.op x y)))))) := by
    first
    | (have i₁ := eq20463
       have i₂ := eq9015 sF1
       grind)
    | exact superpose eq9015 eq20463
    | exact resolve eq20463 eq9015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9015 eq20463
  have eq20810 : (M.op (M.op x y) (M.op y (M.op x y))) = (τ (M.op y (M.op (M.op x y) (σ (M.op x y))))) := by
    first
    | exact superpose eq20559 eq9145
    | exact resolve eq9145 eq20559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20559
  have eq20821 : (M.op y (M.op y (M.op x y))) = (τ (M.op y (M.op (M.op x y) (σ (M.op x y))))) := by
    first
    | exact superpose eq4137 eq20810
    | exact resolve eq20810 eq4137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4137 eq20810
  have eq31477 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq119 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq31477
    | exact resolve eq31477 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31477
  have eq31495 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq31484
       have r₂ := eq27
       grind)
    | exact resolve eq31484 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31484
  have eq31499 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq31495
    | exact resolve eq31495 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31495
  have eq31503 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq31499
    | exact resolve eq31499 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31499
  have eq31868 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31503 eq67
    | (have r₁ := eq67
       have r₂ := eq31503
       grind)
    | exact resolve eq67 eq31503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq31897 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31503 eq8881
    | exact resolve eq8881 eq31503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8881 eq31503
  have eq31947 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq31868
  have eq33394 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31897 eq9207
    | exact resolve eq9207 eq31897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9207 eq31897
  have eq34783 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31947 eq119
    | exact resolve eq119 eq31947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq31947
  have eq34797 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34783
  have eq34802 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34797 eq33394
    | exact resolve eq33394 eq34797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33394 eq34797
  have eq34845 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq34802
  have eq34856 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq34845
       have r₂ := eq27
       grind)
    | exact resolve eq34845 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34845
  have eq34916 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq34856
       grind)
    | exact superpose eq34856 eq56
    | exact resolve eq56 eq34856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq34856
  have eq34997 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq34916 eq9145
    | exact resolve eq9145 eq34916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9145 eq34916
  have eq35054 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq53 eq34997
    | exact resolve eq34997 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq34997
  have eq36046 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq35054 eq12432
    | exact resolve eq12432 eq35054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12432 eq35054
  have eq36061 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9139 eq36046
    | exact resolve eq36046 eq9139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9139 eq36046
  have eq38339 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq36061 eq821
    | exact resolve eq821 eq36061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821 eq36061
  have eq38426 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq38339
    | exact resolve eq38339 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq38339
  have eq38445 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq38426
    | exact resolve eq38426 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq38426
  have eq38451 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq38445
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq38445
    | exact resolve eq38445 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38445
  have eq38452 : x = (M.op x y) ∨ x = y := by grind
  clear eq38451
  have eq38455 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq38452 eq20
    | exact resolve eq20 eq38452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38452
  have eq38649 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq38455
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38455
    | exact resolve eq38455 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38455
  have eq38733 : x = (M.op x (τ (M.op y (M.op (M.op x y) (σ (M.op x y)))))) ∨ x = y := by
    first
    | exact superpose eq38649 eq20558
    | exact resolve eq20558 eq38649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20558
  have eq38747 : x = (M.op x (M.op y (M.op y (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq20821 eq38733
    | exact resolve eq38733 eq20821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20821 eq38733
  have eq38800 : x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq10490 eq38747
    | exact resolve eq38747 eq10490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10490 eq38747
  have eq39824 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq521 y
       have i₂ := eq38800
       grind)
    | exact superpose eq38800 eq521
    | exact resolve eq521 eq38800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq38800
  have eq39916 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq39824
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39824
    | exact resolve eq39824 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39824
  have eq39931 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq39916
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39916
    | exact resolve eq39916 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39916
  have eq39936 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq39931
    | exact resolve eq39931 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39931
  have eq39937 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq39936 eq27
    | exact resolve eq27 eq39936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39936
  have eq40024 : x = y := by
    first
    | (have r₁ := eq39937
       have r₂ := eq38649
       grind)
    | exact resolve eq39937 eq38649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38649 eq39937
  have eq40028 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq40024
       grind)
    | exact superpose eq40024 eq18
    | exact resolve eq18 eq40024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq40029 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq40024
       grind)
    | exact superpose eq40024 eq24
    | exact resolve eq24 eq40024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq40024
  have eq40222 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq40029
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq40029
    | exact resolve eq40029 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq40029
  have eq40242 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40222 eq26
    | exact resolve eq26 eq40222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq40222
  have eq42619 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq40242 eq74
    | exact resolve eq74 eq40242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq40242
  have eq42752 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq42619
       have i₂ := eq40028
       grind)
    | exact superpose eq40028 eq42619
    | exact resolve eq42619 eq40028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40028 eq42619
  have eq42805 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42752 eq15
    | exact resolve eq15 eq42752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42752
  have eq42863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq42805
    | exact resolve eq42805 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq42805
  have eq42884 : False := by grind
  exact eq42884

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxx_pxx_pxy_Equation1560 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X0
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq47 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (τ X0)
       have i₂ := eq52 (τ X0)
       grind)
    | exact superpose eq52 eq20
    | exact resolve eq20 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq92 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq92
    | exact resolve eq92 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq92
  have eq104 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq100 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq168 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq27 (σ X0) (σ X0)
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq27
    | exact resolve eq27 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq104 X1
       grind)
    | exact superpose eq104 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq326 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq292 x y
       grind)
    | exact superpose eq292 eq16
    | (have j1 := eq292 x y
       grind)
    | exact resolve eq16 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq816 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq326
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq326
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq326
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq326
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq326 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq817 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq816
  have eq88995 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq817
       grind)
    | exact superpose eq817 eq16
    | exact resolve eq16 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq88996 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq88995
       have r₂ := eq104 x
       grind)
    | exact resolve eq88995 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88995
  have eq2217211 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq88996
       grind)
    | exact superpose eq88996 eq10
    | exact resolve eq10 eq88996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88996
  have eq2217844 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2217211
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2217211
    | exact resolve eq2217211 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217211
  have eq2217886 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2217844
       grind)
    | exact superpose eq2217844 eq16
    | exact resolve eq16 eq2217844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217844
  have eq2217887 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq2217886
       have r₂ := eq104 x
       grind)
    | exact resolve eq2217886 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq2217886
  have eq2218093 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2217887
       grind)
    | exact superpose eq2217887 eq10
    | exact resolve eq10 eq2217887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217887
  have eq2218996 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2218093
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2218093
    | exact resolve eq2218093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2218093
  have eq2218997 : x = (M.op y y) := by grind
  clear eq2218996
  have eq2219268 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq168 y
       have i₂ := eq2218997
       grind)
    | exact superpose eq2218997 eq168
    | exact resolve eq168 eq2218997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq2219758 : x = (M.op x y) := by
    first
    | (have i₁ := eq27 y y
       have i₂ := eq2218997
       grind)
    | exact superpose eq2218997 eq27
    | exact resolve eq27 eq2218997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2218997
  have eq2265738 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2219268
       grind)
    | exact superpose eq2219268 eq16
    | exact resolve eq16 eq2219268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219268
  have eq2266386 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2265738
       have i₂ := eq2219758
       grind)
    | exact superpose eq2219758 eq2265738
    | exact resolve eq2265738 eq2219758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219758 eq2265738
  have eq2266387 : False := by grind
  exact eq2266387

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyx_pxy_Equation1560 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1560 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  clear eq49
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq78
    | exact resolve eq78 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq79
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79
    | exact resolve eq79 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq96 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq100 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq96
  have eq101 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq100
  have eq132 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq16
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq214 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq53 (M.op y y)
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq221 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq54 (M.op sF3 sF3)
       have i₂ := eq14 sF3 sF3 sF3
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq470 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq59 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq59
    | exact resolve eq59 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq80 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq910 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq909
    | exact resolve eq909 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq913 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq910
       have r₂ := eq28
       grind)
    | exact resolve eq910 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq915 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq913
    | exact resolve eq913 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq941 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq915 eq221
    | exact resolve eq221 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq946 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq941
    | exact resolve eq941 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq1003 : (τ (M.op (σ x) (σ y))) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq946 eq132
    | exact resolve eq132 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq946
  have eq1022 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq59 y y
       have i₂ := eq1003
       grind)
    | exact superpose eq1003 eq59
    | exact resolve eq59 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq1003
  have eq1071 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq915 eq1022
    | exact resolve eq1022 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq1022
  have eq1081 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1071
  have eq1083 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1081
    | exact resolve eq1081 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1084 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1083
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1083
    | exact resolve eq1083 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1085 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1084
  have eq1087 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1085 eq30
    | exact resolve eq30 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1085
  have eq1110 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1087
    | exact resolve eq1087 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1087
  have eq1111 : x = (M.op x y) ∨ x = y := by grind
  clear eq1110
  have eq1114 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1111 eq21
    | exact resolve eq21 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1124 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq1111 eq214
    | exact resolve eq214 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq1111
  have eq1133 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1124
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1124
    | exact resolve eq1124 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1140 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1114
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1114
    | exact resolve eq1114 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1155 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1140 eq27
    | exact resolve eq27 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1188 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq470 y
       have i₂ := eq1133
       grind)
    | exact superpose eq1133 eq470
    | exact resolve eq470 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470 eq1133
  have eq1199 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1188
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1188
    | exact resolve eq1188 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1201 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq1199
    | exact resolve eq1199 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1244 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1201 eq1155
    | exact resolve eq1155 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq1201
  have eq1254 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1244
  have eq1257 : x = y := by
    first
    | (have r₁ := eq1254
       have r₂ := eq28
       grind)
    | exact resolve eq1254 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq1259 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1257
       grind)
    | exact superpose eq1257 eq19
    | exact resolve eq19 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1260 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1257
       grind)
    | exact superpose eq1257 eq25
    | exact resolve eq25 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1257
  have eq1283 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1260
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1260
    | exact resolve eq1260 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1260
  have eq1371 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1283 eq27
    | exact resolve eq27 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1283
  have eq1519 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1371 eq71
    | exact resolve eq71 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1371
  have eq1533 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1519
       have i₂ := eq1259
       grind)
    | exact superpose eq1259 eq1519
    | exact resolve eq1519 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259 eq1519
  have eq1536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1533 eq15
    | exact resolve eq15 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq1562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1536
    | exact resolve eq1536 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1536
  have eq1567 : False := by grind
  exact eq1567

/-- `Equation1577`: `x = (y ◇ z) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_pyx_pyy_pxy_Equation1577 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1577 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1577.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (M.op X2 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op x y) (M.op x (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) (M.op (M.op X1 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X1 X2) (M.op X1 (M.op X2 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op X1 X2) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) (M.op X1 X2) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq90 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X2 (M.op X0 X1))) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X2 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq14 X0 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq14
    | (have j1 := eq11 X1 X0
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1 x
       have i₂ := eq14 X1 x X0
       grind)
    | exact superpose eq14 eq90
    | (have j0 := eq90 X0 X1 x
       grind)
    | exact resolve eq90 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X2 X0) = X2 ∨ (M.op X0 X1) = (k X2 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq11 X0 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X2 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq119 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq120 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq116 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq116 x
       have r₂ := eq13 x x
       grind)
    | exact resolve eq116 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq122 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq120 (σ X0)
       grind)
    | exact superpose eq120 eq10
    | exact resolve eq10 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq120 y
       grind)
    | exact superpose eq120 eq76
    | exact resolve eq76 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq125 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq120 sF2
       grind)
    | exact superpose eq120 eq49
    | exact resolve eq49 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq126 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq125
       have i₂ := eq120 x
       grind)
    | exact superpose eq120 eq125
    | exact resolve eq125 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq127 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq124
       have i₂ := eq120 sF3
       grind)
    | exact superpose eq120 eq124
    | exact resolve eq124 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq122 X0
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq122
    | exact resolve eq122 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq132 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq104
       have i₂ := eq120 sF3
       grind)
    | exact superpose eq120 eq104
    | exact resolve eq104 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq133 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq132
       have i₂ := eq120 y
       grind)
    | exact superpose eq120 eq132
    | exact resolve eq132 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq143 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq144 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq143
       have i₂ := eq120 sF1
       grind)
    | exact superpose eq120 eq143
    | exact resolve eq143 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq147 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq144
       have i₂ := eq120 sF0
       grind)
    | exact superpose eq120 eq144
    | exact resolve eq144 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq168 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq147 eq16
    | exact resolve eq16 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq267 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) X0) y) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq120 (τ X0)
       grind)
    | exact superpose eq120 eq34
    | exact resolve eq34 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq398 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq388 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq388
    | exact resolve eq388 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq400 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq398 X0
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq398
    | exact resolve eq398 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq398
  have eq443 : y = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq53 eq255
    | exact resolve eq255 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq488 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq54 eq267
    | exact resolve eq267 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq488 eq14
    | exact resolve eq14 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq559 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq267 eq56
    | exact resolve eq56 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X1 X0) X1
       have i₂ := eq56 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq280 (M.op x X0)
       have i₂ := eq56 (M.op x X0) x X0
       grind)
    | exact superpose eq56 eq280
    | exact resolve eq280 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq630 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq563 eq14
    | exact resolve eq14 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq670 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) X3)) (M.op (M.op X2 (M.op X0 X1)) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X1 X2 (M.op (M.op X3 X0) X3) X4
       have i₂ := eq56 X1 X3 X0
       grind)
    | exact superpose eq56 eq52
    | exact resolve eq52 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X1 (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 X2 X3 (M.op X2 (M.op (M.op X3 X1) X0))
       have i₂ := eq14 X0 X2 (M.op X3 X1)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) (M.op (M.op X0 (M.op x y)) X1)) = (M.op (M.op X2 y) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ x)) (M.op (M.op X0 (M.op (σ x) (σ y))) X1)) = (M.op (M.op X2 (σ y)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq811 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) = (M.op (M.op (M.op X3 X4) (M.op X1 X2)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X3 (M.op X4 X0)) (M.op X3 X4) X1 X2
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq960 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq93 y x
       grind)
    | exact superpose eq93 eq44
    | (have j1 := eq93 y x
       grind)
    | exact resolve eq44 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq93
  have eq974 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq960
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq960
    | exact resolve eq960 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq976 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq974
    | exact resolve eq974 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq977 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq976
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq976
    | exact resolve eq976 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq1057 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq559 (M.op sF3 (M.op sF4 X0))
       have i₂ := eq14 X0 sF3 sF4
       grind)
    | exact superpose eq14 eq559
    | exact resolve eq559 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq1125 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x y
       have i₂ := eq567 X0
       grind)
    | exact superpose eq567 eq52
    | exact resolve eq52 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq1151 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq630 eq52
    | exact resolve eq52 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq1231 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op X0 x)) y) := by
    intro X0
    first
    | exact superpose eq1125 eq14
    | exact resolve eq14 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1315 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq267 eq1151
    | exact resolve eq1151 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1316 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1151 (M.op sF2 x)
       have i₂ := eq56 sF4 sF2 x
       grind)
    | exact superpose eq56 eq1151
    | exact resolve eq1151 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1325 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X0 (σ x))) (σ y)) := by
    intro X0
    first
    | exact superpose eq1151 eq14
    | exact resolve eq14 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1351 : (M.op (σ x) (M.op (σ y) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1151 eq1057
    | exact resolve eq1057 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057 eq1151
  have eq1352 : (M.op (σ x) (M.op (σ y) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq267 eq1351
    | exact resolve eq1351 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq1351
  have eq1451 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq52 x X0 X0 y
       have i₂ := eq1231 X0
       grind)
    | exact superpose eq1231 eq52
    | exact resolve eq52 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq1600 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) X1)) (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1316 eq14
    | exact resolve eq14 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1606 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X1 (σ y))) := by
    intro X1
    first
    | (have i₁ := eq1600 X1 x
       have i₂ := eq55 sF3 X1 sF2 x
       grind)
    | exact superpose eq55 eq1600
    | exact resolve eq1600 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1600
  have eq1622 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1325 eq52
    | exact resolve eq52 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1325
  have eq3546 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq115 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq3547 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3546 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3546
  have eq3550 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3547 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq3547 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq3547 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3547
  have eq4644 : ∀ X0 : G, y = (M.op x (M.op (σ (M.op X0 X0)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1451 (σ X0)
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq1451
    | exact resolve eq1451 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451
  have eq4645 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ (M.op X0 X0)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1622 (σ X0)
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq1622
    | exact resolve eq1622 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1622
  have eq7822 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq977 eq119
    | (have j0 := eq119 (σ y) (σ x)
       grind)
    | exact resolve eq119 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq7825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq7822
    | exact resolve eq7822 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7822
  have eq7832 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq7825
       have r₂ := eq27
       grind)
    | exact resolve eq7825 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7825
  have eq7838 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq7832
    | exact resolve eq7832 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7832
  have eq7893 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7838 eq1352
    | exact resolve eq1352 eq7838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq9665 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7893 eq522
    | exact resolve eq522 eq7893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq7893
  have eq13112 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq977 eq3550
    | exact resolve eq3550 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977 eq3550
  have eq13210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq13112
    | exact resolve eq13112 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13112
  have eq13214 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq13210
       have r₂ := eq27
       grind)
    | exact resolve eq13210 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13210
  have eq13222 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13214 eq51
    | exact resolve eq51 eq13214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq13245 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ (M.op x y))) X0) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13214 eq560
    | exact resolve eq560 eq13214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13304 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) X0) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13222 eq560
    | exact resolve eq560 eq13222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13222
  have eq13324 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13304 X0
       have i₂ := eq56 X0 sF2 sF1
       grind)
    | exact superpose eq56 eq13304
    | exact resolve eq13304 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13304
  have eq15733 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13245 eq9665
    | exact resolve eq9665 eq13245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9665 eq13245
  have eq15830 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq15733
  have eq15884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15830 eq7838
    | exact resolve eq7838 eq15830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7838 eq15830
  have eq15940 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq15884
  have eq15953 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq15940
       have r₂ := eq27
       grind)
    | exact resolve eq15940 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15940
  have eq15957 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15953 eq27
    | exact resolve eq27 eq15953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15980 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15953 eq1315
    | exact resolve eq1315 eq15953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq16009 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq15953 eq13324
    | exact resolve eq13324 eq15953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13324
  have eq16010 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16009 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16009
  have eq18364 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13214 eq15980
    | exact resolve eq15980 eq13214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15980
  have eq18419 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq18364
  have eq20125 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16010 eq18419
    | exact resolve eq18419 eq16010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16010 eq18419
  have eq20248 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq20125
  have eq20404 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20248 eq168
    | exact resolve eq168 eq20248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq20248
  have eq20479 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq20404
    | exact resolve eq20404 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20404
  have eq21711 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20479 eq443
    | exact resolve eq443 eq20479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq20479
  have eq21879 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq127
       have i₂ := eq21711
       grind)
    | exact superpose eq21711 eq127
    | exact resolve eq127 eq21711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq21711
  have eq21969 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq21879
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21879
    | exact resolve eq21879 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21879
  have eq22936 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21969 eq1606
    | exact resolve eq1606 eq21969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606 eq21969
  have eq23009 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq22936
    | exact resolve eq22936 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22936
  have eq24136 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15953 eq23009
    | exact resolve eq23009 eq15953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15953 eq23009
  have eq24205 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq24136
  have eq25702 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq24205 eq13214
    | exact resolve eq13214 eq24205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13214 eq24205
  have eq25757 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq25702
  have eq25783 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq25757
       have r₂ := eq15957
       grind)
    | exact resolve eq25757 eq15957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15957 eq25757
  have eq25796 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq25783 eq20
    | exact resolve eq20 eq25783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25799 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq25783 eq53
    | exact resolve eq53 eq25783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq25871 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq25796
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25796
    | exact resolve eq25796 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25796
  have eq29216 : ∀ X0 X1 X2 : G, (M.op (M.op X2 y) (M.op X2 X1)) = (M.op (M.op x y) (M.op (M.op (M.op X0 x) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq776 x X0 X2
       have i₂ := eq699 X0 sF0 (M.op x x) x
       grind)
    | (have i₁ := eq776 X2 X0 X2
       have i₂ := eq699 X0 (M.op X2 x) X2 sF0
       grind)
    | exact superpose eq699 eq776
    | exact resolve eq776 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq29217 : ∀ X1 X2 : G, (M.op (M.op X2 y) (M.op X2 X1)) = (M.op (M.op x y) (M.op x X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq29216 x X1 X2
       have i₂ := eq56 X1 x x
       grind)
    | exact superpose eq56 eq29216
    | exact resolve eq29216 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29216
  have eq30204 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ y)) (M.op X2 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 (σ x)) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq777 x X0 X2
       have i₂ := eq699 X0 sF4 (M.op x sF2) x
       grind)
    | (have i₁ := eq777 X2 X0 X2
       have i₂ := eq699 X0 (M.op X2 sF2) X2 sF4
       grind)
    | exact superpose eq699 eq777
    | exact resolve eq777 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq30205 : ∀ X1 X2 : G, (M.op (M.op X2 (σ y)) (M.op X2 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq30204 X1 x X2
       have i₂ := eq56 x X1 sF2
       grind)
    | exact superpose eq56 eq30204
    | exact resolve eq30204 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30204
  have eq45507 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X3 X0) X3))) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq670 X0 X1 X2 X3 X4
       have i₂ := eq699 X4 (M.op X2 (M.op (M.op X3 X0) X3)) X2 (M.op X0 X1)
       grind)
    | (have i₁ := eq670 X0 X1 X3 X3 X0
       have i₂ := eq699 X0 (M.op X0 X1) (M.op X3 (M.op (M.op X3 X0) X3)) X3
       grind)
    | exact superpose eq699 eq670
    | exact resolve eq670 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq699
  have eq46119 : y = (M.op x (M.op (σ y) (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq4644 (M.op x x)
       have i₂ := eq25799 x
       grind)
    | exact superpose eq25799 eq4644
    | exact resolve eq4644 eq25799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644
  have eq46120 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = y := by
    first
    | (have i₁ := eq4645 (M.op x x)
       have i₂ := eq25799 x
       grind)
    | exact superpose eq25799 eq4645
    | exact resolve eq4645 eq25799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645 eq25799
  have eq46229 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = y := by
    first
    | (have i₁ := eq46120
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq46120
    | exact resolve eq46120 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46120
  have eq46230 : y = (M.op x (M.op (σ y) (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq46119
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq46119
    | exact resolve eq46119 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46119
  have eq46518 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq25871 eq46229
    | exact resolve eq46229 eq25871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25871 eq46229
  have eq46610 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = y := by grind
  clear eq46518
  have eq46691 : y = (M.op x (M.op (σ y) x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq25783 eq46230
    | exact resolve eq46230 eq25783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25783 eq46230
  have eq46762 : y = (M.op x (M.op (σ y) x)) ∨ x = y := by grind
  clear eq46691
  have eq47602 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq46610 eq560
    | exact resolve eq560 eq46610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46610
  have eq47653 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq47602 X0
       have i₂ := eq56 X0 sF3 sF4
       grind)
    | exact superpose eq56 eq47602
    | exact resolve eq47602 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47602
  have eq49311 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq46762 eq560
    | exact resolve eq560 eq46762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq46762
  have eq52015 : (M.op y y) = (τ (M.op y (σ y))) ∨ x = y := by
    first
    | exact superpose eq49311 eq133
    | exact resolve eq133 eq49311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq49311
  have eq58016 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X2 (M.op (M.op (M.op X3 X0) X3) (M.op X0 (M.op X1 X4)))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq45507 X0 X1 X2 X3 X4
       have i₂ := eq811 X4 X2 (M.op (M.op X3 X0) X3) X0 X1
       grind)
    | exact superpose eq811 eq45507
    | exact resolve eq45507 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq45507
  have eq58017 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X0 (M.op X0 (M.op X1 X4)))))) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq58016 X0 X1 X2 x X4
       have i₂ := eq56 (M.op X0 (M.op X1 X4)) x X0
       grind)
    | exact superpose eq56 eq58016
    | exact resolve eq58016 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq58016
  have eq78291 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op y (σ y)) (M.op y (σ y))) ∨ x = y := by
    first
    | exact superpose eq52015 eq400
    | exact resolve eq400 eq52015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq52015
  have eq78306 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op y y) (M.op y y))) ∨ x = y := by
    first
    | exact superpose eq30205 eq78291
    | exact resolve eq78291 eq30205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30205 eq78291
  have eq78309 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq78306
       have i₂ := eq29217 y y
       grind)
    | exact superpose eq29217 eq78306
    | exact resolve eq78306 eq29217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29217 eq78306
  have eq78311 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq78309
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78309
    | exact resolve eq78309 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78309
  have eq78313 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq26 eq78311
    | exact resolve eq78311 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78311
  have eq78314 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq147 eq78313
    | exact resolve eq78313 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq78313
  have eq78343 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq78314 eq47653
    | exact resolve eq47653 eq78314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47653 eq78314
  have eq78437 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq78343
  have eq78904 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op (σ (M.op x y)) (σ (M.op x y)))))))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq78437 eq58017
    | exact resolve eq58017 eq78437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78437
  have eq78915 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq78904 x x
       have i₂ := eq58017 x sF1 x sF1
       grind)
    | (have i₁ := eq78904 x x
       have i₂ := eq58017 x x x (M.op sF1 (M.op x (M.op x (M.op x (M.op x (M.op sF1 sF1))))))
       grind)
    | exact superpose eq58017 eq78904
    | exact resolve eq78904 eq58017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58017 eq78904
  have eq78958 : x = y := by
    first
    | (have r₁ := eq78915
       have r₂ := eq27
       grind)
    | exact resolve eq78915 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78915
  have eq78986 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq78958
       grind)
    | exact superpose eq78958 eq18
    | exact resolve eq18 eq78958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq78987 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq78958
       grind)
    | exact superpose eq78958 eq24
    | exact resolve eq24 eq78958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq78958
  have eq79080 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq78987
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78987
    | exact resolve eq78987 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq78987
  have eq79089 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq79080 eq26
    | exact resolve eq26 eq79080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq79080
  have eq79449 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq79089 eq126
    | exact resolve eq126 eq79089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq79089
  have eq79613 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq79449
       have i₂ := eq78986
       grind)
    | exact superpose eq78986 eq79449
    | exact resolve eq79449 eq78986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78986 eq79449
  have eq79634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq79613 eq15
    | exact resolve eq15 eq79613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79613
  have eq79677 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq79634
    | exact resolve eq79634 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq79634
  have eq79686 : False := by grind
  exact eq79686

/-- `Equation1577`: `x = (y ◇ z) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyx_pxy_Equation1577 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1577 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1577.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (M.op X2 X0))) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op x y) (M.op x (M.op y X0))) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) (M.op (M.op X1 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X1 X2) (M.op X1 (M.op X2 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op X1 X2) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) (M.op X1 X2) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  clear eq49
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq78
    | exact resolve eq78 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq79
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79
    | exact resolve eq79 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq89 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq100 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq96
  have eq101 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq100
  have eq122 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq122
  have eq126 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq125
  have eq132 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq16
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq293 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq304 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq293 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq293
    | exact resolve eq293 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq305 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq304
  have eq370 : y = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq56 eq214
    | exact resolve eq214 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq460 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq218 eq59
    | exact resolve eq59 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X2 (M.op X1 X0) X1
       have i₂ := eq59 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 (M.op (M.op X2 X1) (M.op X2 X0)) X2 X1
       have i₂ := eq14 X0 (M.op X2 X1) X2
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 : G, y = (M.op X0 (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq56 eq59
    | exact resolve eq59 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq57 eq59
    | exact resolve eq59 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x X0)) y) := by
    intro X0
    first
    | exact superpose eq463 eq14
    | exact resolve eq14 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq505 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq464 eq14
    | exact resolve eq14 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) X3)) (M.op (M.op X2 (M.op X0 X1)) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X1 X2 (M.op (M.op X3 X0) X3) X4
       have i₂ := eq59 X1 X3 X0
       grind)
    | exact superpose eq59 eq55
    | exact resolve eq55 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X1 (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X1 X2 X3 (M.op X2 (M.op (M.op X3 X1) X0))
       have i₂ := eq14 X0 X2 (M.op X3 X1)
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) (M.op (M.op X0 (M.op x y)) X1)) = (M.op (M.op X2 y) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ x)) (M.op (M.op X0 (M.op (σ x) (σ y))) X1)) = (M.op (M.op X2 (σ y)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq58
    | exact resolve eq58 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op x (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq58
    | exact resolve eq58 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq732 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) = (M.op (M.op (M.op X3 X4) (M.op X1 X2)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58 (M.op X3 (M.op X4 X0)) (M.op X3 X4) X1 X2
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X1 (M.op (M.op X3 X0) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X1 X3 X0 (M.op X3 X2)
       have i₂ := eq58 X2 X3 X0 X1
       grind)
    | exact superpose eq58 eq55
    | exact resolve eq55 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq460 (M.op sF3 (M.op sF4 X0))
       have i₂ := eq14 X0 sF3 sF4
       grind)
    | exact superpose eq14 eq460
    | exact resolve eq460 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq927 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq55 X0 X0 x y
       have i₂ := eq489 X0
       grind)
    | exact superpose eq489 eq55
    | exact resolve eq55 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq949 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq505 eq55
    | exact resolve eq55 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq1002 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq927 (M.op x x)
       have i₂ := eq59 sF0 x x
       grind)
    | exact superpose eq59 eq927
    | exact resolve eq927 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1010 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op X0 x)) y) := by
    intro X0
    first
    | exact superpose eq927 eq14
    | exact resolve eq14 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq1130 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq218 eq949
    | exact resolve eq949 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1139 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X0 (σ x))) (σ y)) := by
    intro X0
    first
    | exact superpose eq949 eq14
    | exact resolve eq14 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1164 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq949 eq814
    | exact resolve eq814 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq949
  have eq1165 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq218 eq1164
    | exact resolve eq1164 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq1164
  have eq1362 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 (M.op x X1)) (M.op X0 y)) := by
    intro X0 X1
    first
    | exact superpose eq1002 eq14
    | exact resolve eq14 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1369 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op x (M.op X1 y)) := by
    intro X1
    first
    | (have i₁ := eq1362 x X1
       have i₂ := eq58 y x x X1
       grind)
    | exact superpose eq58 eq1362
    | exact resolve eq1362 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq1362
  have eq1434 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq55 x X0 X0 y
       have i₂ := eq1010 X0
       grind)
    | exact superpose eq1010 eq55
    | exact resolve eq55 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1533 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1139 eq55
    | exact resolve eq55 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1636 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq464 eq461
    | exact resolve eq461 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq1815 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ y) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq1636 eq59
    | exact resolve eq59 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2005 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1636 eq462
    | exact resolve eq462 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq1636
  have eq4044 : ∀ X0 : G, y = (M.op x (M.op (σ (M.op X0 X0)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1434 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq1434
    | exact resolve eq1434 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434
  have eq4545 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ (M.op X0 X0)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1533 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq1533
    | exact resolve eq1533 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1533
  have eq5151 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq722 (M.op x y) y
       have i₂ := eq489 y
       grind)
    | exact superpose eq489 eq722
    | exact resolve eq722 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq722
  have eq5214 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq5151
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq5151
    | exact resolve eq5151 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5151
  have eq6785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq80 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq6785
    | exact resolve eq6785 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6785
  have eq6789 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq6786
       have r₂ := eq28
       grind)
    | exact resolve eq6786 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6786
  have eq6791 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq6789
    | exact resolve eq6789 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6789
  have eq6796 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6791 eq89
    | (have r₁ := eq89
       have r₂ := eq6791
       grind)
    | exact resolve eq89 eq6791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq6804 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (σ x)) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq6791 eq460
    | exact resolve eq460 eq6791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq6809 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6791 eq1130
    | exact resolve eq1130 eq6791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq6791
  have eq6827 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq6796
  have eq6828 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq6827
  have eq6836 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1815 eq6804
    | exact resolve eq6804 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815 eq6804
  have eq7017 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6828 eq80
    | exact resolve eq80 eq6828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq6828
  have eq7021 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq7017
  have eq7095 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7021 eq57
    | exact resolve eq57 eq7021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq7279 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6836 eq1139
    | exact resolve eq1139 eq6836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq7338 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq7279
       have i₂ := eq461 sF2 sF4 sF3
       grind)
    | exact superpose eq461 eq7279
    | exact resolve eq7279 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7279
  have eq7460 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7021 eq6809
    | exact resolve eq6809 eq7021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6809 eq7021
  have eq7489 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq7460
  have eq7504 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7489 eq2005
    | exact resolve eq2005 eq7489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005 eq7489
  have eq13616 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7504 eq6836
    | exact resolve eq6836 eq7504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6836
  have eq13651 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13616
  have eq13675 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1165 eq13651
    | exact resolve eq13651 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165 eq13651
  have eq13718 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13675 eq7095
    | exact resolve eq7095 eq13675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7095 eq13675
  have eq13760 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13718
  have eq13835 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13760 eq165
    | exact resolve eq165 eq13760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq13760
  have eq13889 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq13835
    | exact resolve eq13835 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13835
  have eq14616 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13889 eq370
    | exact resolve eq370 eq13889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq13889
  have eq14756 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq14616
       grind)
    | exact superpose eq14616 eq101
    | exact resolve eq101 eq14616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq14616
  have eq14824 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14756
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14756
    | exact resolve eq14756 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14756
  have eq17233 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14824 eq7504
    | exact resolve eq7504 eq14824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7504 eq14824
  have eq17285 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq17233
  have eq17322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17285 eq7338
    | exact resolve eq7338 eq17285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7338 eq17285
  have eq17361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq17322
  have eq17378 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq17361
       have r₂ := eq28
       grind)
    | exact resolve eq17361 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17361
  have eq17395 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17378 eq30
    | exact resolve eq30 eq17378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17378
  have eq17458 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq17395
    | exact resolve eq17395 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17395
  have eq17459 : x = (M.op x y) ∨ x = y := by grind
  clear eq17458
  have eq17463 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq17459 eq21
    | exact resolve eq21 eq17459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17466 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17459 eq56
    | exact resolve eq56 eq17459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq17507 : (M.op x x) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq17459 eq5214
    | exact resolve eq5214 eq17459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5214 eq17459
  have eq17512 : (M.op x x) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq17507
       have i₂ := eq1369 x
       grind)
    | exact superpose eq1369 eq17507
    | exact resolve eq17507 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369 eq17507
  have eq17535 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq17463
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17463
    | exact resolve eq17463 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17463
  have eq18305 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op x (M.op (M.op X0 X1) (M.op X1 (M.op x x)))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq17512 eq752
    | exact resolve eq752 eq17512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17512
  have eq18310 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18305 X0 x
       have i₂ := eq752 x x x X0
       grind)
    | exact superpose eq752 eq18305
    | exact resolve eq18305 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752 eq18305
  have eq19673 : ∀ X0 X1 X2 : G, (M.op (M.op X2 y) (M.op X2 X1)) = (M.op (M.op x y) (M.op (M.op (M.op X0 x) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq697 x X0 X2
       have i₂ := eq629 X0 sF0 (M.op x x) x
       grind)
    | (have i₁ := eq697 X2 X0 X2
       have i₂ := eq629 X0 (M.op X2 x) X2 sF0
       grind)
    | exact superpose eq629 eq697
    | exact resolve eq697 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq19674 : ∀ X1 X2 : G, (M.op (M.op X2 y) (M.op X2 X1)) = (M.op (M.op x y) (M.op x X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq19673 x X1 X2
       have i₂ := eq59 X1 x x
       grind)
    | exact superpose eq59 eq19673
    | exact resolve eq19673 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19673
  have eq20202 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ y)) (M.op X2 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 (σ x)) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq698 x X0 X2
       have i₂ := eq629 X0 sF4 (M.op x sF2) x
       grind)
    | (have i₁ := eq698 X2 X0 X2
       have i₂ := eq629 X0 (M.op X2 sF2) X2 sF4
       grind)
    | exact superpose eq629 eq698
    | exact resolve eq698 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq20203 : ∀ X1 X2 : G, (M.op (M.op X2 (σ y)) (M.op X2 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq20202 X1 x X2
       have i₂ := eq59 x X1 sF2
       grind)
    | exact superpose eq59 eq20202
    | exact resolve eq20202 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20202
  have eq34039 : y = (M.op x (M.op (σ y) (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq4044 (M.op x x)
       have i₂ := eq17466 x
       grind)
    | exact superpose eq17466 eq4044
    | exact resolve eq4044 eq17466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4044
  have eq34041 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = y := by
    first
    | (have i₁ := eq4545 (M.op x x)
       have i₂ := eq17466 x
       grind)
    | exact superpose eq17466 eq4545
    | exact resolve eq4545 eq17466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4545 eq17466
  have eq34127 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = y := by
    first
    | (have i₁ := eq34041
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34041
    | exact resolve eq34041 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34041
  have eq34128 : y = (M.op x (M.op (σ y) (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq34039
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34039
    | exact resolve eq34039 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34039
  have eq34698 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq17535 eq34127
    | exact resolve eq34127 eq17535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17535 eq34127
  have eq34762 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = y := by grind
  clear eq34698
  have eq34823 : y = (M.op x (M.op (σ y) x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq18310 eq34128
    | exact resolve eq34128 eq18310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18310 eq34128
  have eq34873 : y = (M.op x (M.op (σ y) x)) ∨ x = y := by grind
  clear eq34823
  have eq35945 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) X0) = (M.op (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq34762 eq461
    | exact resolve eq461 eq34762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34762
  have eq35988 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35945 X0
       have i₂ := eq59 X0 sF3 sF4
       grind)
    | exact superpose eq59 eq35945
    | exact resolve eq35945 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35945
  have eq36021 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X3 X0) X3))) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq602 X0 X1 X2 X3 X4
       have i₂ := eq629 X4 (M.op X2 (M.op (M.op X3 X0) X3)) X2 (M.op X0 X1)
       grind)
    | (have i₁ := eq602 X0 X1 X3 X3 X0
       have i₂ := eq629 X0 (M.op X0 X1) (M.op X3 (M.op (M.op X3 X0) X3)) X3
       grind)
    | exact superpose eq629 eq602
    | exact resolve eq602 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq629
  have eq36038 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq34873 eq461
    | exact resolve eq461 eq34873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq34873
  have eq38638 : (M.op y y) = (τ (M.op y (σ y))) ∨ x = y := by
    first
    | exact superpose eq36038 eq132
    | exact resolve eq132 eq36038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq36038
  have eq43157 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X2 (M.op (M.op (M.op X3 X0) X3) (M.op X0 (M.op X1 X4)))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq36021 X0 X1 X2 X3 X4
       have i₂ := eq732 X4 X2 (M.op (M.op X3 X0) X3) X0 X1
       grind)
    | exact superpose eq732 eq36021
    | exact resolve eq36021 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732 eq36021
  have eq43158 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X0 (M.op X0 (M.op X1 X4)))))) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq43157 X0 X1 X2 x X4
       have i₂ := eq59 (M.op X0 (M.op X1 X4)) x X0
       grind)
    | exact superpose eq59 eq43157
    | exact resolve eq43157 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq43157
  have eq61693 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op y (σ y)) (M.op y (σ y))) ∨ x = y := by
    first
    | exact superpose eq38638 eq305
    | exact resolve eq305 eq38638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq38638
  have eq61712 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq20203 eq61693
    | exact resolve eq61693 eq20203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20203 eq61693
  have eq61715 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq27 eq61712
    | exact resolve eq61712 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61712
  have eq61717 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq61715
       have i₂ := eq19674 y y
       grind)
    | exact superpose eq19674 eq61715
    | exact resolve eq61715 eq19674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19674 eq61715
  have eq61719 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq61717
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61717
    | exact resolve eq61717 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61717
  have eq61720 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq126 eq61719
    | exact resolve eq61719 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq61719
  have eq61733 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq61720 eq35988
    | exact resolve eq35988 eq61720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35988 eq61720
  have eq61821 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq61733
  have eq62516 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op (σ (M.op x y)) (σ (M.op x y)))))))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq61821 eq43158
    | exact resolve eq43158 eq61821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61821
  have eq62521 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq62516 x x
       have i₂ := eq43158 x sF1 x sF1
       grind)
    | (have i₁ := eq62516 x x
       have i₂ := eq43158 x x x (M.op sF1 (M.op x (M.op x (M.op x (M.op x (M.op sF1 sF1))))))
       grind)
    | exact superpose eq43158 eq62516
    | exact resolve eq62516 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43158 eq62516
  have eq62564 : x = y := by
    first
    | (have r₁ := eq62521
       have r₂ := eq28
       grind)
    | exact resolve eq62521 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62521
  have eq62591 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq62564
       grind)
    | exact superpose eq62564 eq19
    | exact resolve eq19 eq62564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq62592 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq62564
       grind)
    | exact superpose eq62564 eq25
    | exact resolve eq25 eq62564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq62564
  have eq62672 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq62592
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq62592
    | exact resolve eq62592 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq62592
  have eq63070 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq62672 eq27
    | exact resolve eq27 eq62672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq62672
  have eq65382 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq63070 eq71
    | exact resolve eq71 eq63070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq63070
  have eq65517 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq65382
       have i₂ := eq62591
       grind)
    | exact superpose eq62591 eq65382
    | exact resolve eq65382 eq62591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62591 eq65382
  have eq65531 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65517 eq15
    | exact resolve eq15 eq65517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65517
  have eq65577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq65531
    | exact resolve eq65531 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq65531
  have eq65586 : False := by grind
  exact eq65586
