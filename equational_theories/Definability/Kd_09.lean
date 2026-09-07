import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation417`: `x = x ◇ (x ◇ (y ◇ (x ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation417 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law417 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law417.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq47 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq76 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq16
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq426 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47
    | exact resolve eq47 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq466 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq426 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq426
    | (have j0 := eq426 X0 X1
       grind)
    | exact resolve eq426 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq906 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq76
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq76
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq76
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq76 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq907 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq906
  have eq4485 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq907
       grind)
    | exact superpose eq907 eq16
    | exact resolve eq16 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4489 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq907
       grind)
    | exact superpose eq907 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq907
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq907
       grind)
    | exact resolve eq13 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq4491 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4489
  have eq4492 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4491
  have eq4495 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4492
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4492
    | exact resolve eq4492 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4492
  have eq7086 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq466 x y
       have i₂ := eq4495
       grind)
    | exact superpose eq4495 eq466
    | (have j0 := eq466 x y
       grind)
    | exact resolve eq466 eq4495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466 eq4495
  have eq7129 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq7086
  have eq7156 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7129
       have r₂ := eq4485
       grind)
    | exact resolve eq7129 eq4485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4485 eq7129
  have eq7346 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq7156
       grind)
    | exact superpose eq7156 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq7156
       grind)
    | exact resolve eq13 eq7156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7348 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq7346
  have eq7349 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq7348
  have eq7544 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq80 x y
       have i₂ := eq7349
       grind)
    | exact superpose eq7349 eq80
    | (have j0 := eq80 x y
       grind)
    | exact resolve eq80 eq7349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq7349
  have eq7554 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7544
  have eq7555 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7554
  have eq7613 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq7555
       grind)
    | exact superpose eq7555 eq16
    | exact resolve eq16 eq7555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7555
  have eq7782 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7613
       have i₂ := eq7156
       grind)
    | exact superpose eq7156 eq7613
    | exact resolve eq7613 eq7156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7156 eq7613
  have eq7783 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7782
  have eq7784 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq7783
  have eq7943 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7784
       grind)
    | exact superpose eq7784 eq10
    | exact resolve eq10 eq7784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7784
  have eq8011 : x = y ∨ x = y := by
    first
    | (have i₁ := eq7943
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7943
    | exact resolve eq7943 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7943
  have eq8012 : x = y := by grind
  clear eq8011
  have eq8216 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8012
       grind)
    | exact superpose eq8012 eq16
    | exact resolve eq16 eq8012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8012
  have eq8217 : False := by grind
  exact eq8217

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,Y) = Y then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_x_pxy_x_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq24 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq43 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq24 X0
       grind)
    | exact resolve eq13 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq85 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq44 (τ X1) X0
       grind)
    | exact superpose eq44 eq19
    | (have j1 := eq44 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq44 (σ X1) (σ X0)
       grind)
    | exact superpose eq44 eq15
    | (have j1 := eq44 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq155 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq172 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq155 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq155
    | (have j0 := eq155 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq155 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq479 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86 x y
       grind)
    | exact superpose eq86 eq16
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq495 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq479
       have i₂ := eq172 y x
       grind)
    | exact superpose eq172 eq479
    | (have j1 := eq172 (σ x) (σ y)
       grind)
    | (have r₁ := eq479
       have r₂ := eq172 y x
       grind)
    | (have r₁ := eq479
       have r₂ := eq172 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq479
       have r₂ := eq172 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq479 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq479
  have eq496 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq495
  have eq542 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq496
       grind)
    | exact superpose eq496 eq10
    | exact resolve eq10 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq573 : x = y ∨ x = y := by
    first
    | (have i₁ := eq542
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq542
    | exact resolve eq542 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq574 : x = y := by grind
  clear eq573
  have eq624 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq574
       grind)
    | exact superpose eq574 eq16
    | exact resolve eq16 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq625 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq624
       have i₂ := eq24 x
       grind)
    | exact superpose eq24 eq624
    | exact resolve eq624 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq626 : False := by grind
  exact eq626

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,Y) = Y then m(Y,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_x_pyx_x_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq43 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq24 X0
       grind)
    | exact resolve eq13 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq85 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq44 (τ X0) X1
       grind)
    | exact superpose eq44 eq19
    | (have j1 := eq44 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq44 (σ X0) (σ X1)
       grind)
    | exact superpose eq44 eq15
    | (have j1 := eq44 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq155 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
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
  have eq178 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq155 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq155
    | (have j0 := eq155 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq155 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq479 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86 x y
       grind)
    | exact superpose eq86 eq16
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq495 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq479
       have i₂ := eq178 x y
       grind)
    | exact superpose eq178 eq479
    | (have j1 := eq178 (σ x) (σ y)
       grind)
    | (have r₁ := eq479
       have r₂ := eq178 x y
       grind)
    | (have r₁ := eq479
       have r₂ := eq178 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq479
       have r₂ := eq178 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq479 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq479
  have eq496 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq495
  have eq542 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq496
       grind)
    | exact superpose eq496 eq10
    | exact resolve eq10 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq573 : x = y ∨ x = y := by
    first
    | (have i₁ := eq542
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq542
    | exact resolve eq542 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq574 : x = y := by grind
  clear eq573
  have eq624 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq574
       grind)
    | exact superpose eq574 eq16
    | exact resolve eq16 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq625 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq624
       have i₂ := eq24 x
       grind)
    | exact superpose eq24 eq624
    | exact resolve eq624 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq626 : False := by grind
  exact eq626

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation419 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq48 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq80 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47 x y
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 x y
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq411 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48
    | exact resolve eq48 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq445 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq411 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq411
    | (have j0 := eq411 X0 X1
       grind)
    | exact resolve eq411 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq824 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq80
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq80
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq80
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq80
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq80 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq825 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq824
  have eq5171 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq825
       grind)
    | exact superpose eq825 eq16
    | exact resolve eq16 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5174 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq825
       grind)
    | exact superpose eq825 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq825
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq825
       grind)
    | exact resolve eq13 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq5185 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq5174
  have eq5186 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq5185
  have eq5194 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5186
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq5186
    | exact resolve eq5186 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5186
  have eq8165 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq445 x y
       have i₂ := eq5194
       grind)
    | exact superpose eq5194 eq445
    | (have j0 := eq445 x y
       grind)
    | exact resolve eq445 eq5194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq8168 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq5194
       grind)
    | exact superpose eq5194 eq10
    | exact resolve eq10 eq5194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5194
  have eq8215 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8165
  have eq8242 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8168
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8168
    | exact resolve eq8168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8168
  have eq8243 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8215
       have r₂ := eq5171
       grind)
    | exact resolve eq8215 eq5171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5171 eq8215
  have eq8246 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq8242
       have r₂ := eq13 x y
       grind)
    | exact resolve eq8242 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8242
  have eq8627 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq84 x y
       have i₂ := eq8246
       grind)
    | exact superpose eq8246 eq84
    | (have j0 := eq84 x y
       grind)
    | exact resolve eq84 eq8246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq8246
  have eq8639 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8627
  have eq8640 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8639
  have eq8836 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq8640
       grind)
    | exact superpose eq8640 eq16
    | exact resolve eq16 eq8640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8640
  have eq9059 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8836
       have i₂ := eq8243
       grind)
    | exact superpose eq8243 eq8836
    | exact resolve eq8836 eq8243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8243 eq8836
  have eq9060 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9059
  have eq9061 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq9060
  have eq9221 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9061
       grind)
    | exact superpose eq9061 eq10
    | exact resolve eq10 eq9061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9061
  have eq9296 : x = y ∨ x = y := by
    first
    | (have i₁ := eq9221
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9221
    | exact resolve eq9221 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9221
  have eq9297 : x = y := by grind
  clear eq9296
  have eq9462 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9297
       grind)
    | exact superpose eq9297 eq16
    | exact resolve eq16 eq9297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9297
  have eq9463 : False := by grind
  exact eq9463

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation422 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq47 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq106 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48 x y
       grind)
    | exact superpose eq48 eq16
    | (have j1 := eq48 x y
       grind)
    | exact resolve eq16 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq419 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47
    | exact resolve eq47 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq448 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq419
    | (have j0 := eq419 X0 X1
       grind)
    | exact resolve eq419 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq801 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq106
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq106
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq106
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq106
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq106 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq802 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq801
  have eq7979 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq802
       grind)
    | exact superpose eq802 eq16
    | exact resolve eq16 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7985 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq802
       grind)
    | exact superpose eq802 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq802
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq802
       grind)
    | exact resolve eq13 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq8015 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq7985
  have eq8016 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8015
  have eq8018 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8016
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq8016
    | exact resolve eq8016 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8016
  have eq8528 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq448 y x
       have i₂ := eq8018
       grind)
    | exact superpose eq8018 eq448
    | (have j0 := eq448 y x
       grind)
    | exact resolve eq448 eq8018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq8529 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq8018
       grind)
    | exact superpose eq8018 eq10
    | exact resolve eq10 eq8018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8018
  have eq8568 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8528
  have eq8598 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8529
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8529
    | exact resolve eq8529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8529
  have eq8599 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8568
       have r₂ := eq7979
       grind)
    | exact resolve eq8568 eq7979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7979 eq8568
  have eq8602 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq8598
       have r₂ := eq13 x y
       grind)
    | exact resolve eq8598 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8598
  have eq8889 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq111 x y
       have i₂ := eq8602
       grind)
    | exact superpose eq8602 eq111
    | (have j0 := eq111 x y
       grind)
    | exact resolve eq111 eq8602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq8602
  have eq8903 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8889
  have eq8904 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8903
  have eq9040 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq8904
       grind)
    | exact superpose eq8904 eq16
    | exact resolve eq16 eq8904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8904
  have eq9213 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9040
       have i₂ := eq8599
       grind)
    | exact superpose eq8599 eq9040
    | exact resolve eq9040 eq8599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8599 eq9040
  have eq9214 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9213
  have eq9215 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq9214
  have eq9363 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9215
       grind)
    | exact superpose eq9215 eq10
    | exact resolve eq10 eq9215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9215
  have eq9427 : x = y ∨ x = y := by
    first
    | (have i₁ := eq9363
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9363
    | exact resolve eq9363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9363
  have eq9428 : x = y := by grind
  clear eq9427
  have eq9583 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9428
       grind)
    | exact superpose eq9428 eq16
    | exact resolve eq16 eq9428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9428
  have eq9584 : False := by grind
  exact eq9584

/-- `Equation4279`: `x ◇ (x ◇ x) = y ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pyx_pxy_Equation4279 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4279 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4279.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq25 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X4 X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq9 x X3 X4
       have i₂ := eq9 x X0 X1
       grind)
    | (have i₁ := eq9 x X1 x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X2 X3) X3
       have i₂ := eq9 X0 X3 X2
       grind)
    | (have i₁ := eq9 X0 (M.op X0 X0) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op X3 X2)) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq40
    | (have j0 := eq40 X0 X1
       grind)
    | exact resolve eq40 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq69 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X4 X5) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq25 X2 X3 (M.op X4 X5) X5
       have i₂ := eq25 X5 X4 X0 X1
       grind)
    | (have i₁ := eq25 X2 X3 (M.op X4 X5) X5
       have i₂ := eq25 X0 X1 X5 X4
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op (M.op X4 X5) (M.op X0 (M.op X1 X0))) ∨ (M.op X2 X3) = (k X2 X3) ∨ X2 = X3 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq42 X3 X2 (M.op X4 X5) X5
       have i₂ := eq25 X5 X4 X0 X1
       grind)
    | (have i₁ := eq42 X3 X2 (M.op X4 X5) X5
       have i₂ := eq25 X0 X1 X5 X4
       grind)
    | exact superpose eq25 eq42
    | (have j0 := eq42 X3 X2 X2 X3
       grind)
    | exact resolve eq42 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq42 (σ y) (σ x) X0 X1
       grind)
    | exact superpose eq42 eq16
    | (have j1 := eq42 (σ y) (σ x) x x
       grind)
    | (have r₁ := eq16
       have r₂ := eq42 (σ (M.op x y)) (M.op (σ x) (σ y)) x x
       grind)
    | (have r₁ := eq16
       have r₂ := eq42 (M.op (σ x) (σ y)) (σ (M.op x y)) x x
       grind)
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq392 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 X1
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq365
    | (have j0 := eq365 X0 X1
       grind)
    | exact resolve eq365 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq423 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ X3) (σ X0)) ∨ (M.op X3 X0) = (k X3 X0) ∨ X0 = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X3 X1 X2
       have i₂ := eq14 X3 X0
       grind)
    | (have i₁ := eq69 X0 X1 X2
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq69
    | (have j1 := eq14 X3 X0
       grind)
    | exact resolve eq69 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ (M.op X3 (M.op X3 X3))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 (M.op X3 (M.op X3 X3)) X1 X2
       have i₂ := eq28 X3 X0 X3 (M.op X3 X3)
       grind)
    | exact superpose eq28 eq69
    | exact resolve eq69 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq69
  have eq671 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq45 X1 X0
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq10
    | (have j1 := eq45 X1 X0
       grind)
    | exact resolve eq10 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq689 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq671 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq671
    | (have j0 := eq671 X0 X1
       grind)
    | exact resolve eq671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq1314 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op X4 (M.op X5 X4)) = (M.op (M.op X6 X7) (M.op (M.op X0 X1) (M.op X2 (M.op X3 X2)))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq25 X4 X5 (M.op X6 X7) X7
       have i₂ := eq84 X2 X3 X7 X6 X0 X1
       grind)
    | (have i₁ := eq25 X0 X1 (M.op X0 (M.op X1 X0)) (M.op X4 X5)
       have i₂ := eq84 X0 X1 X2 X3 X4 X5
       grind)
    | exact superpose eq84 eq25
    | exact resolve eq25 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq62524 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (σ (M.op (M.op X2 (M.op X2 X2)) (M.op X2 (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (M.op X2 (M.op X2 X2))
       have i₂ := eq424 X2 X0 X1 X2
       grind)
    | exact superpose eq424 eq23
    | exact resolve eq23 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq64656 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62524 X2 X3 x
       have i₂ := eq328 x x X0 X1 x (M.op x x)
       grind)
    | (have i₁ := eq62524 X0 X1 X2
       have i₂ := eq328 X0 X1 (M.op X2 (M.op X2 X2)) (M.op X2 (M.op X2 X2)) x x
       grind)
    | exact superpose eq328 eq62524
    | (have j1 := eq328 X0 X1 X0 X1 x x
       grind)
    | exact resolve eq62524 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq64660 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (σ (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62524 X2 X3 x
       have i₂ := eq84 x x X0 X1 x (M.op x x)
       grind)
    | exact superpose eq84 eq62524
    | exact resolve eq62524 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq62524
  have eq66860 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (σ (M.op X3 X0)) ∨ (M.op (σ X3) (σ X0)) = (σ (k X3 X0)) ∨ (σ X0) = (σ X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64660 X3 X3 X1 X2
       have i₂ := eq689 X0 X3
       grind)
    | (have i₁ := eq64660 X0 X1 X2 X3
       have i₂ := eq689 (M.op X1 X0) X1
       grind)
    | exact superpose eq689 eq64660
    | (have j1 := eq689 X0 X3
       grind)
    | exact resolve eq64660 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq64660
  have eq131800 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq392 (M.op x (M.op x x)) (M.op x x)
       have i₂ := eq1314 x x x x X0 X1 x (M.op x x)
       grind)
    | (have i₁ := eq392 x x
       have i₂ := eq1314 X0 X1 x x x x x x
       grind)
    | exact superpose eq1314 eq392
    | (have j0 := eq392 X0 X1
       grind)
    | exact resolve eq392 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq1314
  have eq132307 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq66860 y x x x
       grind)
    | (have r₁ := eq131800 x x
       have r₂ := eq66860 y x x x
       grind)
    | exact resolve eq131800 eq66860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66860 eq131800
  have eq132314 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq132307
       grind)
    | exact superpose eq132307 eq16
    | exact resolve eq16 eq132307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132307
  have eq154689 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op x y) = (k x y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq423 y X0 X1 x
       grind)
    | exact superpose eq423 eq16
    | (have j1 := eq423 y X1 x x
       grind)
    | (have r₁ := eq16
       have r₂ := eq423 (σ (M.op x y)) X1 x (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq423 (M.op (σ x) (σ y)) X1 x (σ (M.op x y))
       grind)
    | exact resolve eq16 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq154690 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have j1 := eq64656 x y x x
       grind)
    | (have r₁ := eq154689 x x
       have r₂ := eq64656 x y x x
       grind)
    | (have r₁ := eq154689 x x
       have r₂ := eq64656 (σ (M.op x y)) (M.op x (M.op x x)) x x
       grind)
    | (have r₁ := eq154689 x x
       have r₂ := eq64656 (M.op x (M.op x x)) (σ (M.op x y)) x x
       grind)
    | exact resolve eq154689 eq64656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64656 eq154689
  have eq154694 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq132314
       have i₂ := eq154690
       grind)
    | exact superpose eq154690 eq132314
    | exact resolve eq132314 eq154690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132314 eq154690
  have eq154695 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq154694
  have eq154812 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq154695
       grind)
    | exact superpose eq154695 eq10
    | exact resolve eq10 eq154695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154695
  have eq154874 : x = y ∨ x = y := by
    first
    | (have i₁ := eq154812
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq154812
    | exact resolve eq154812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154812
  have eq154875 : x = y := by grind
  clear eq154874
  have eq155118 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq154875
       grind)
    | exact superpose eq154875 eq16
    | exact resolve eq16 eq154875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154875
  have eq155119 : False := by grind
  exact eq155119

/-- `Equation4290`: `x ◇ (x ◇ y) = y ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pyx_Equation4290 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4290 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4290.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq59 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) (τ X1)
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq64 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq72 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq74 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq59 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq229 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq71 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq230 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq229 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq234 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq230 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq230 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq230 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq243 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq234 (σ X0)
       grind)
    | exact superpose eq234 eq15
    | exact resolve eq15 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq234 (τ X0)
       grind)
    | exact superpose eq234 eq34
    | exact resolve eq34 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq248 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq245 X0
       have i₂ := eq234 X0
       grind)
    | exact superpose eq234 eq245
    | exact resolve eq245 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq250 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq243 X0
       have i₂ := eq234 X0
       grind)
    | exact superpose eq234 eq243
    | exact resolve eq243 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq342 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq250 X0
       grind)
    | exact superpose eq250 eq9
    | exact resolve eq9 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq250 X0
       grind)
    | exact superpose eq250 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq250 X0
       grind)
    | exact superpose eq250 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq248 X0
       grind)
    | exact superpose eq248 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X0)) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq72 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq72 eq15
    | (have j1 := eq72 (σ X0) X2 X2
       grind)
    | exact resolve eq15 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq800 : ∀ X0 X1 X2 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq770 X0 X1 X2
       have i₂ := eq250 X1
       grind)
    | exact superpose eq250 eq770
    | (have j0 := eq770 X0 X1 X2
       grind)
    | exact resolve eq770 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq998 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq74 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1001 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq998 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq2258 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq1001 (σ X0) X1
       grind)
    | exact superpose eq1001 eq30
    | (have j1 := eq1001 (σ X0) X1
       grind)
    | exact resolve eq30 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2261 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1001 (τ X0) X1
       grind)
    | exact superpose eq1001 eq17
    | (have j1 := eq1001 (τ X0) X1
       grind)
    | exact resolve eq17 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2278 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1001 (σ X0) (σ X1)
       grind)
    | exact superpose eq1001 eq15
    | (have j1 := eq1001 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2285 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1001 X0 (τ X1)
       grind)
    | exact superpose eq1001 eq17
    | (have j1 := eq1001 X0 (τ X1)
       grind)
    | exact resolve eq17 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1001
  have eq2310 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2278 X0 X1
       have i₂ := eq250 X0
       grind)
    | exact superpose eq250 eq2278
    | (have j0 := eq2278 X0 X1
       grind)
    | exact resolve eq2278 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2278
  have eq2321 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2261 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2261
    | (have j0 := eq2261 X0 X1
       grind)
    | exact resolve eq2261 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261
  have eq2324 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq2351 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2310 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2310
    | (have j0 := eq2310 X0 X1
       grind)
    | exact resolve eq2310 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310
  have eq2353 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2321 X0 X1
       have i₂ := eq248 X0
       grind)
    | exact superpose eq248 eq2321
    | (have j0 := eq2321 X0 X1
       grind)
    | exact resolve eq2321 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq2321
  have eq2356 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2324 X0 X1
       have i₂ := eq250 X0
       grind)
    | exact superpose eq250 eq2324
    | (have j0 := eq2324 X0 X1
       grind)
    | exact resolve eq2324 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2324
  have eq4323 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68
    | (have j0 := eq68 X0 X1
       grind)
    | exact resolve eq68 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq4529 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4323 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4323
    | (have j0 := eq4323 X0 X0
       grind)
    | exact resolve eq4323 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4323
  have eq7293 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq344 X0 X1
       have i₂ := eq4529 X2 X0
       grind)
    | exact superpose eq4529 eq344
    | (have j0 := eq344 X0 X1
       have j1 := eq4529 X2 X0
       grind)
    | exact resolve eq344 eq4529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq4529
  have eq7332 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq7293 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7293
  have eq63825 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2285 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2285
    | (have j0 := eq2285 X1 X1
       grind)
    | exact resolve eq2285 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2285
  have eq64160 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63825 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq63825
    | (have j0 := eq63825 X0 X1
       grind)
    | exact resolve eq63825 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63825
  have eq80467 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq800 X1 X0 X2
       grind)
    | exact superpose eq800 eq10
    | (have j1 := eq800 X1 X0 X2
       grind)
    | exact resolve eq10 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq81320 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80467 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq80467
    | (have j0 := eq80467 X0 X1 X2
       grind)
    | exact resolve eq80467 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80467
  have eq184904 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (k X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq2353 X0 X1
       grind)
    | exact superpose eq2353 eq11
    | (have j1 := eq2353 X0 X1
       grind)
    | exact resolve eq11 eq2353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353
  have eq184929 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq184904 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq184904
    | (have j0 := eq184904 X0 X1
       grind)
    | exact resolve eq184904 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184904
  have eq186835 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq184929 X0 X1
       grind)
    | exact superpose eq184929 eq18
    | (have j1 := eq184929 X0 X1
       grind)
    | exact resolve eq18 eq184929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184929
  have eq194845 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (σ (M.op (τ (σ X0)) X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0
       have i₂ := eq186835 (σ X0) X1
       grind)
    | exact superpose eq186835 eq250
    | (have j1 := eq186835 (σ X0) X1
       grind)
    | exact resolve eq250 eq186835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186835
  have eq194849 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq194845 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq194845
    | (have j0 := eq194845 X0 X1
       grind)
    | exact resolve eq194845 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194845
  have eq194858 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq194849 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq194849
    | (have j0 := eq194849 X0 X1
       grind)
    | exact resolve eq194849 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194849
  have eq194862 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq194858 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq194858
    | (have j0 := eq194858 X0 X1
       grind)
    | exact resolve eq194858 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194858
  have eq197883 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (k X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq2356 X0 X1
       grind)
    | exact superpose eq2356 eq10
    | (have j1 := eq2356 X0 X1
       grind)
    | exact resolve eq10 eq2356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2356
  have eq197908 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq197883 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq197883
    | (have j0 := eq197883 X0 X1
       grind)
    | exact resolve eq197883 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197883
  have eq199567 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq197908 X0 (σ X1)
       grind)
    | exact superpose eq197908 eq15
    | (have j1 := eq197908 X0 (σ X1)
       grind)
    | exact resolve eq15 eq197908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197908
  have eq199589 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq199567 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq199567
    | (have j0 := eq199567 X0 X1
       grind)
    | exact resolve eq199567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199567
  have eq201674 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq199589 x y
       grind)
    | exact superpose eq199589 eq16
    | (have j1 := eq199589 x y
       grind)
    | exact resolve eq16 eq199589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199589
  have eq201709 : x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq64160 y x
       grind)
    | (have r₁ := eq201674
       have r₂ := eq64160 y x
       grind)
    | exact resolve eq201674 eq64160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64160 eq201674
  have eq277538 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2351 x y
       grind)
    | exact superpose eq2351 eq16
    | (have j1 := eq2351 x y
       grind)
    | exact resolve eq16 eq2351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2351
  have eq277544 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have j1 := eq194862 x y
       grind)
    | (have r₁ := eq277538
       have r₂ := eq194862 x y
       grind)
    | exact resolve eq277538 eq194862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194862 eq277538
  have eq277588 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq277544
       grind)
    | exact superpose eq277544 eq10
    | exact resolve eq10 eq277544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277544
  have eq277633 : (σ x) = (σ (M.op x x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq277588
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq277588
    | exact resolve eq277588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277588
  have eq277647 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq343 x X0
       have i₂ := eq277633
       grind)
    | exact superpose eq277633 eq343
    | (have j0 := eq343 x X0
       grind)
    | (have r₁ := eq343 x x
       have r₂ := eq277633
       grind)
    | exact resolve eq343 eq277633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277633
  have eq277689 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq277647 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277647
  have eq277755 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op (σ x) X0)) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq30 x X0
       have i₂ := eq277689 X0
       grind)
    | exact superpose eq277689 eq30
    | exact resolve eq30 eq277689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277768 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq277689 (σ X0)
       grind)
    | exact superpose eq277689 eq15
    | exact resolve eq15 eq277689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277689
  have eq277878 : ∀ X0 : G, (τ (σ x)) ≠ (k x (τ (σ x))) ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq440 (σ x) X0
       have i₂ := eq277755 (σ x)
       grind)
    | exact superpose eq277755 eq440
    | (have j0 := eq440 (σ x) X0
       grind)
    | exact resolve eq440 eq277755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277755
  have eq277894 : ∀ X0 : G, x ≠ (k x x) ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq277878 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq277878
    | (have j0 := eq277878 X0
       grind)
    | exact resolve eq277878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277878
  have eq277913 : ∀ X0 : G, x ≠ (M.op x x) ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq277894 X0
       have i₂ := eq234 x
       grind)
    | exact superpose eq234 eq277894
    | (have j0 := eq277894 X0
       grind)
    | exact resolve eq277894 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277894
  have eq277925 : ∀ X0 : G, (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq277913 X0
       grind)
    | (have r₁ := eq277913 X0
       have r₂ := eq201709
       grind)
    | exact resolve eq277913 eq201709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201709 eq277913
  have eq277930 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq277925 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq277925
    | exact resolve eq277925 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277925
  have eq278224 : x ≠ (M.op x y) ∨ x = (k x y) := by grind
  have eq278264 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq277768 y
       grind)
    | exact superpose eq277768 eq16
    | exact resolve eq16 eq277768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277768
  have eq278406 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq278264
       have i₂ := eq277930 y
       grind)
    | exact superpose eq277930 eq278264
    | exact resolve eq278264 eq277930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277930 eq278264
  have eq278448 : x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq278406
  have eq278452 : x = (k x y) := by
    first
    | (have r₁ := eq278448
       have r₂ := eq278224
       grind)
    | exact resolve eq278448 eq278224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278224 eq278448
  have eq283989 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq81320 y x X0
       grind)
    | exact superpose eq81320 eq16
    | (have j1 := eq81320 y x X0
       grind)
    | exact resolve eq16 eq81320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81320
  have eq283996 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op X0 X0) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq283989 X0
       have j1 := eq7332 x X0 X0
       grind)
    | (have r₁ := eq283989 X0
       have r₂ := eq7332 x x y
       grind)
    | exact resolve eq283989 eq7332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7332 eq283989
  have eq284044 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq234 (σ x)
       have i₂ := eq283996 (σ x)
       grind)
    | exact superpose eq283996 eq234
    | (have j1 := eq283996 (σ x)
       grind)
    | exact resolve eq234 eq283996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283996
  have eq284155 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq284044
  have eq284197 : (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq284155
       have i₂ := eq250 x
       grind)
    | exact superpose eq250 eq284155
    | exact resolve eq284155 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq284155
  have eq284219 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq343 x X0
       have i₂ := eq284197
       grind)
    | exact superpose eq284197 eq343
    | (have j0 := eq343 x X0
       grind)
    | (have r₁ := eq343 x x
       have r₂ := eq284197
       grind)
    | exact resolve eq343 eq284197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284224 : (M.op x x) = (τ (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq284197
       grind)
    | exact superpose eq284197 eq10
    | exact resolve eq10 eq284197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284197
  have eq284279 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq284219 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284219
  have eq284300 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq284224
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq284224
    | exact resolve eq284224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284224
  have eq284926 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op (σ x) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq30 x X0
       have i₂ := eq284279 X0
       grind)
    | exact superpose eq284279 eq30
    | exact resolve eq30 eq284279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq284940 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq284279 (σ X0)
       grind)
    | exact superpose eq284279 eq15
    | exact resolve eq15 eq284279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284279
  have eq285725 : ∀ X0 : G, (τ (σ x)) ≠ (k x (τ (σ x))) ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq440 (σ x) X0
       have i₂ := eq284926 (σ x)
       grind)
    | exact superpose eq284926 eq440
    | (have j0 := eq440 (σ x) X0
       grind)
    | exact resolve eq440 eq284926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq284926
  have eq285744 : ∀ X0 : G, x ≠ (k x x) ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq285725 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq285725
    | (have j0 := eq285725 X0
       grind)
    | exact resolve eq285725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285725
  have eq285754 : ∀ X0 : G, x ≠ (M.op x x) ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq285744 X0
       have i₂ := eq234 x
       grind)
    | exact superpose eq234 eq285744
    | (have j0 := eq285744 X0
       grind)
    | exact resolve eq285744 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq285744
  have eq285759 : ∀ X0 : G, (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq285754 X0
       grind)
    | (have r₁ := eq285754 X0
       have r₂ := eq284300
       grind)
    | exact resolve eq285754 eq284300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284300 eq285754
  have eq285762 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq285759 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq285759
    | exact resolve eq285759 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285759
  have eq286010 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq285762 (τ X0)
       grind)
    | exact superpose eq285762 eq18
    | exact resolve eq18 eq285762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq285762
  have eq287141 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq284940 y
       grind)
    | exact superpose eq284940 eq16
    | exact resolve eq16 eq284940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284940
  have eq287210 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq287141
       have i₂ := eq278452
       grind)
    | exact superpose eq278452 eq287141
    | exact resolve eq287141 eq278452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287141
  have eq289983 : ∀ X0 : G, (σ (M.op x X0)) = (k (σ x) (σ X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq286010 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq286010
    | exact resolve eq286010 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286010
  have eq290062 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op x X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq289983 X0
       have i₂ := eq15 x X0
       grind)
    | exact superpose eq15 eq289983
    | exact resolve eq289983 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289983
  have eq290075 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq290062 y
       have i₂ := eq278452
       grind)
    | exact superpose eq278452 eq290062
    | exact resolve eq290062 eq278452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278452 eq290062
  have eq290244 : y = (M.op y y) := by
    first
    | (have r₁ := eq290075
       have r₂ := eq287210
       grind)
    | exact resolve eq290075 eq287210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287210 eq290075
  have eq290265 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq9 y X0
       have i₂ := eq290244
       grind)
    | exact superpose eq290244 eq9
    | exact resolve eq9 eq290244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290266 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq290244
       grind)
    | exact superpose eq290244 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq290244
       grind)
    | exact resolve eq12 eq290244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290301 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq343 y X0
       have i₂ := eq290244
       grind)
    | exact superpose eq290244 eq343
    | (have j0 := eq343 y X0
       grind)
    | exact resolve eq343 eq290244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq290499 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq290301 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290301
  have eq290501 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq290266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290266
  have eq292346 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq290499 (σ X0)
       grind)
    | exact superpose eq290499 eq15
    | exact resolve eq15 eq290499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290499
  have eq292589 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq292346 X0
       have i₂ := eq290501 X0
       grind)
    | exact superpose eq290501 eq292346
    | exact resolve eq292346 eq290501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290501 eq292346
  have eq295123 : ∀ X0 : G, (M.op (σ X0) (σ (M.op y y))) = (M.op (σ y) (σ (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq342 y (σ X0)
       have i₂ := eq292589 X0
       grind)
    | exact superpose eq292589 eq342
    | exact resolve eq342 eq292589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq295290 : ∀ X0 : G, (M.op (σ X0) (σ (M.op y y))) = (σ (M.op y (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq295123 X0
       have i₂ := eq292589 (M.op y X0)
       grind)
    | exact superpose eq292589 eq295123
    | exact resolve eq295123 eq292589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292589 eq295123
  have eq295394 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq295290 X0
       have i₂ := eq290265 X0
       grind)
    | exact superpose eq290265 eq295290
    | exact resolve eq295290 eq290265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290265 eq295290
  have eq295442 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq295394 X0
       have i₂ := eq290244
       grind)
    | exact superpose eq290244 eq295394
    | exact resolve eq295394 eq290244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290244 eq295394
  have eq297391 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq295442 x
       grind)
    | exact superpose eq295442 eq16
    | (have r₁ := eq16
       have r₂ := eq295442 x
       grind)
    | exact resolve eq16 eq295442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295442
  have eq297563 : False := by grind
  exact eq297563

/-- `Equation432`: `x = x ◇ (y ◇ (x ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation432 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law432 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law432.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq41 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq78 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40 x y
       grind)
    | exact superpose eq40 eq16
    | (have j1 := eq40 x y
       grind)
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq374 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41
    | exact resolve eq41 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq410 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq374
    | (have j0 := eq374 X0 X1
       grind)
    | exact resolve eq374 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq791 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq78
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq78
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq78
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq78 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq792 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq791
  have eq6908 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq792
       grind)
    | exact superpose eq792 eq16
    | exact resolve eq16 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6910 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq792
       grind)
    | exact superpose eq792 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq792
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq792
       grind)
    | exact resolve eq13 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq6917 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq6910
  have eq6918 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq6917
  have eq6926 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6918
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq6918
    | exact resolve eq6918 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6918
  have eq18089 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq410 x y
       have i₂ := eq6926
       grind)
    | exact superpose eq6926 eq410
    | (have j0 := eq410 x y
       grind)
    | exact resolve eq410 eq6926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq18094 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq6926
       grind)
    | exact superpose eq6926 eq10
    | exact resolve eq10 eq6926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6926
  have eq18157 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18089
  have eq18191 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18094
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq18094
    | exact resolve eq18094 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18094
  have eq18192 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18157
       have r₂ := eq6908
       grind)
    | exact resolve eq18157 eq6908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6908 eq18157
  have eq18195 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq18191
       have r₂ := eq13 x y
       grind)
    | exact resolve eq18191 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18191
  have eq18385 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq82 x y
       have i₂ := eq18195
       grind)
    | exact superpose eq18195 eq82
    | (have j0 := eq82 x y
       grind)
    | exact resolve eq82 eq18195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq18195
  have eq18405 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18385
  have eq18406 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18405
  have eq19686 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq18406
       grind)
    | exact superpose eq18406 eq16
    | exact resolve eq16 eq18406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18406
  have eq20066 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19686
       have i₂ := eq18192
       grind)
    | exact superpose eq18192 eq19686
    | exact resolve eq19686 eq18192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18192 eq19686
  have eq20067 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20066
  have eq20068 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq20067
  have eq20340 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20068
       grind)
    | exact superpose eq20068 eq10
    | exact resolve eq10 eq20068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20068
  have eq20427 : x = y ∨ x = y := by
    first
    | (have i₁ := eq20340
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20340
    | exact resolve eq20340 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20340
  have eq20428 : x = y := by grind
  clear eq20427
  have eq20742 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20428
       grind)
    | exact superpose eq20428 eq16
    | exact resolve eq16 eq20428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20428
  have eq20743 : False := by grind
  exact eq20743
