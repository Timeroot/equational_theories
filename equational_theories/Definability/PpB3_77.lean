import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_y_pxy_pyx_Equation450 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law450 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq40 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq28
    | exact resolve eq28 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq63 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X1
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X1
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq12 (M.op X1 X0) X0
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq74 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 (τ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 (τ X0))
       have i₂ := eq71 X1 (τ X0)
       grind)
    | exact superpose eq71 eq18
    | exact resolve eq18 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X1 (σ X0)) X0
       have i₂ := eq71 X1 (σ X0)
       grind)
    | exact superpose eq71 eq22
    | exact resolve eq22 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : ∀ X0 X1 : G, (k (σ (M.op X1 (τ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq74
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq662 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) ∨ (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq662 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq667 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq681 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq22
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq22 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq692 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 (τ X0)))) = X0 ∨ (M.op X0 (σ (M.op X1 (τ X0)))) = X0 ∨ (σ (M.op X1 (τ X0))) = (M.op (σ (M.op X1 (τ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq14 (σ (M.op X1 (τ X0))) X0
       grind)
    | exact superpose eq14 eq77
    | (have j1 := eq14 (σ (M.op X1 (τ X0))) X0
       grind)
    | exact resolve eq77 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 X1 : G, (σ (M.op X1 (τ X0))) = (M.op (σ (M.op X1 (τ X0))) X0) ∨ (M.op X0 (σ (M.op X1 (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq692 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq6983 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq667 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq667
    | (have j0 := eq667 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq667 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6989 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) ∨ (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq667 (M.op X1 X0) X0
       have i₂ := eq71 X1 X0
       grind)
    | exact superpose eq71 eq667
    | (have j0 := eq667 (M.op X1 X0) X0
       grind)
    | exact resolve eq667 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq7133 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq6989 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6989
  have eq7261 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X1))) = (k (σ X1) (σ (M.op X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq663 (σ (M.op X1 X0)) (σ X0)
       have i₂ := eq7133 X0 X1
       grind)
    | exact superpose eq7133 eq663
    | (have j1 := eq7133 X1 X0
       grind)
    | exact resolve eq663 eq7133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7271 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X1))) = (k (σ X1) (σ (M.op X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq7261 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7261
  have eq7275 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X1))) = (σ (k X1 (M.op X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7271 X0 X1
       have i₂ := eq15 X1 (M.op X0 X1)
       grind)
    | exact superpose eq15 eq7271
    | (have j0 := eq7271 X0 X1
       grind)
    | exact resolve eq7271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7271
  have eq7607 : ∀ X0 X1 : G, (k (k (σ (τ X0)) X1) X0) = X0 ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 (τ X1)
       have i₂ := eq686 X1 (τ X0)
       grind)
    | exact superpose eq686 eq77
    | (have j1 := eq686 X1 (τ X0)
       grind)
    | exact resolve eq77 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq7708 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X0)) ∨ (k (k X0 X1) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7607 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7607
    | (have j0 := eq7607 X0 X1
       grind)
    | exact resolve eq7607 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7607
  have eq8369 : ∀ X0 X1 : G, (k (k (τ (σ X0)) X1) X0) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (σ X1)
       have i₂ := eq681 X1 (σ X0)
       grind)
    | exact superpose eq681 eq76
    | (have j1 := eq681 X1 (σ X0)
       grind)
    | exact resolve eq76 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq8426 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (k X0 X1) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8369 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8369
    | (have j0 := eq8369 X0 X1
       grind)
    | exact resolve eq8369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8369
  have eq9003 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = X1 ∨ (k (k X1 X0) X1) = X1 ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X1 (τ X0)
       have i₂ := eq7708 X1 X0
       grind)
    | exact superpose eq7708 eq77
    | (have j1 := eq7708 X1 X0
       grind)
    | exact resolve eq77 eq7708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7708
  have eq9060 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X0)) ∨ (k (k X1 X0) X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9003 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9003
    | (have j0 := eq9003 X0 X1
       grind)
    | exact resolve eq9003 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9003
  have eq10475 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 (σ (τ X0))) = X1 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq719 X0 (τ X1)
       have i₂ := eq9060 X0 X1
       grind)
    | exact superpose eq9060 eq719
    | (have j1 := eq9060 X1 X0
       grind)
    | exact resolve eq719 eq9060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq10531 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 (σ (τ X0))) = X1 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10475 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10475
    | (have j0 := eq10475 X0 X1
       grind)
    | exact resolve eq10475 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10475
  have eq10533 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10531 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10531
    | (have j0 := eq10531 X0 X1
       grind)
    | exact resolve eq10531 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10531
  have eq10535 : ∀ X0 X1 : G, (k (k X0 X1) X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq10533 X0 X1
       have j1 := eq12 (k X0 X1) X0
       grind)
    | (have r₁ := eq10533 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10533 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10533 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10533
  have eq52806 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6983 x y
       grind)
    | exact superpose eq6983 eq16
    | (have j1 := eq6983 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq6983 x y
       grind)
    | exact resolve eq16 eq6983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6983
  have eq52893 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq52806
  have eq64095 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (k (k X1 X0) X1) = X1 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X1 (σ X0)
       have i₂ := eq8426 X1 X0
       grind)
    | exact superpose eq8426 eq76
    | (have j1 := eq8426 X1 X0
       grind)
    | exact resolve eq76 eq8426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8426
  have eq64220 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (k X1 X0) X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64095 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq64095
    | (have j0 := eq64095 X0 X1
       grind)
    | exact resolve eq64095 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64095
  have eq64280 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (τ X0) = (k (k (τ X0) X1) (τ X0)) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64220 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64220
    | (have j0 := eq64220 X1 (τ X0)
       grind)
    | exact resolve eq64220 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64321 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k (k x y) x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64220 y x
       grind)
    | exact superpose eq64220 eq16
    | (have j1 := eq64220 y x
       grind)
    | exact resolve eq16 eq64220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64220
  have eq64437 : (σ x) ≠ (σ x) ∨ x = (k (k x y) x) ∨ x = (k y x) := by
    first
    | exact superpose eq10535 eq64321
    | (have j1 := eq10535 x y
       grind)
    | exact resolve eq64321 eq10535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10535 eq64321
  have eq64438 : x = (k (k x y) x) ∨ x = (k y x) := by grind
  clear eq64437
  have eq64447 : ∀ X0 X1 : G, (τ X0) = (τ (k (k X0 (σ X1)) X0)) ∨ (M.op X0 (σ X1)) = X0 ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64280 X0 X1
       have i₂ := eq40 X0 X1 X0
       grind)
    | exact superpose eq40 eq64280
    | (have j0 := eq64280 X0 X1
       grind)
    | exact resolve eq64280 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq64280
  have eq74938 : ∀ X0 X1 : G, (τ (σ (M.op X1 (τ (σ X0))))) = (τ (k (σ X0) (σ (M.op X1 (τ (σ X0)))))) ∨ (σ (M.op X1 (τ (σ X0)))) = (M.op (σ (M.op X1 (τ (σ X0)))) (σ X0)) ∨ (τ (σ (M.op X1 (τ (σ X0))))) = (k X0 (τ (σ (M.op X1 (τ (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq64447 (σ (M.op X1 (τ (σ X0)))) X0
       have i₂ := eq77 (σ X0) X1
       grind)
    | exact superpose eq77 eq64447
    | (have j0 := eq64447 (σ (M.op X1 (τ (σ X0)))) X0
       grind)
    | exact resolve eq64447 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq64447
  have eq75299 : ∀ X0 X1 : G, (τ (σ (M.op X1 (τ (σ X0))))) = (k (τ (σ X0)) (M.op X1 (τ (σ X0)))) ∨ (σ (M.op X1 (τ (σ X0)))) = (M.op (σ (M.op X1 (τ (σ X0)))) (σ X0)) ∨ (τ (σ (M.op X1 (τ (σ X0))))) = (k X0 (τ (σ (M.op X1 (τ (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq74938 X0 X1
       have i₂ := eq22 (σ X0) (M.op X1 (τ (σ X0)))
       grind)
    | exact superpose eq22 eq74938
    | (have j0 := eq74938 X0 X1
       grind)
    | exact resolve eq74938 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq74938
  have eq75406 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = (τ (σ (M.op X1 X0))) ∨ (σ (M.op X1 (τ (σ X0)))) = (M.op (σ (M.op X1 (τ (σ X0)))) (σ X0)) ∨ (τ (σ (M.op X1 (τ (σ X0))))) = (k X0 (τ (σ (M.op X1 (τ (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq75299 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75299
    | (have j0 := eq75299 X0 X1
       grind)
    | exact resolve eq75299 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75299
  have eq75478 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (σ (M.op X1 (τ (σ X0)))) = (M.op (σ (M.op X1 (τ (σ X0)))) (σ X0)) ∨ (τ (σ (M.op X1 (τ (σ X0))))) = (k X0 (τ (σ (M.op X1 (τ (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq75406 X0 X1
       have i₂ := eq10 (M.op X1 X0)
       grind)
    | exact superpose eq10 eq75406
    | (have j0 := eq75406 X0 X1
       grind)
    | exact resolve eq75406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75406
  have eq75535 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (τ (σ (M.op X1 (τ (σ X0))))) = (k X0 (τ (σ (M.op X1 (τ (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq75478 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75478
    | (have j0 := eq75478 X0 X1
       grind)
    | exact resolve eq75478 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75478
  have eq75577 : ∀ X0 X1 : G, (M.op X1 (τ (σ X0))) = (k X0 (M.op X1 (τ (σ X0)))) ∨ (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75535 X0 X1
       have i₂ := eq10 (M.op X1 (τ (σ X0)))
       grind)
    | exact superpose eq10 eq75535
    | (have j0 := eq75535 X0 X1
       grind)
    | exact resolve eq75535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75535
  have eq75611 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75577 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75577
    | (have j0 := eq75577 X0 X1
       grind)
    | exact resolve eq75577 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75577
  have eq75612 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq75611 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75611
  have eq108532 : ∀ X0 X1 : G, (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7275 (τ X1) (τ X0)
       have i₂ := eq9060 X0 X1
       grind)
    | exact superpose eq9060 eq7275
    | (have j1 := eq9060 X1 X0
       grind)
    | exact resolve eq7275 eq9060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7275 eq9060
  have eq108691 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq108532 X0 X1
       have i₂ := eq17 X1 (τ X0)
       grind)
    | exact superpose eq17 eq108532
    | (have j0 := eq108532 X0 X1
       grind)
    | exact resolve eq108532 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq108532
  have eq108714 : ∀ X0 X1 : G, (k X1 X0) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq108691 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq108691
    | (have j0 := eq108691 X0 X1
       grind)
    | exact resolve eq108691 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108691
  have eq108724 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq108714 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq108714
    | (have j0 := eq108714 X0 X1
       grind)
    | exact resolve eq108714 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108714
  have eq108731 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq108724 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq108724
    | (have j0 := eq108724 X0 X1
       grind)
    | exact resolve eq108724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108724
  have eq108737 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq108731 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq108731
    | (have j0 := eq108731 X0 X1
       grind)
    | exact resolve eq108731 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108731
  have eq108740 : ∀ X0 X1 : G, (k (k X0 X1) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq108737 X0 X1
       have j1 := eq12 (k X0 X1) X0
       grind)
    | (have r₁ := eq108737 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq108737 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108737
  have eq108750 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq108740 (M.op X1 X0) X0
       have i₂ := eq71 X1 X0
       grind)
    | exact superpose eq71 eq108740
    | (have j0 := eq108740 (M.op X1 X0) X0
       grind)
    | exact resolve eq108740 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq109034 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq108750 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108750
  have eq109403 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq109034 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116982 : x = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq76 x (σ y)
       have i₂ := eq52893
       grind)
    | exact superpose eq52893 eq76
    | exact resolve eq76 eq52893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52893
  have eq117093 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq116982
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq116982
    | exact resolve eq116982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116982
  have eq117123 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq117093
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq117093
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq117093
       have r₂ := eq12 y x
       grind)
    | exact resolve eq117093 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117093
  have eq117178 : y = (k (τ (σ x)) y) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76 y (σ x)
       have i₂ := eq117123
       grind)
    | exact superpose eq117123 eq76
    | exact resolve eq76 eq117123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq117123
  have eq117288 : y = (k x y) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117178
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq117178
    | exact resolve eq117178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117178
  have eq117311 : y = (k x y) ∨ x = (k y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq117288
       have r₂ := eq12 x y
       grind)
    | exact resolve eq117288 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117288
  have eq117349 : x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq117311 eq64438
    | exact resolve eq64438 eq117311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64438 eq117311
  have eq117371 : x = (k y x) := by grind
  clear eq117349
  have eq117391 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq117371
       grind)
    | exact superpose eq117371 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq117371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117397 : y = (k x y) ∨ (M.op x y) = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq108740 y x
       have i₂ := eq117371
       grind)
    | exact superpose eq117371 eq108740
    | (have j0 := eq108740 y x
       grind)
    | exact resolve eq108740 eq117371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108740 eq117371
  have eq117398 : (M.op x y) = (k x y) ∨ y = (k x y) := by grind
  clear eq117397
  have eq117404 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq117391
  have eq117423 : ∀ X0 : G, x = (M.op x (M.op y (M.op X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq117404
       grind)
    | exact superpose eq117404 eq9
    | exact resolve eq9 eq117404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117434 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq663 y x
       have i₂ := eq117404
       grind)
    | exact superpose eq117404 eq663
    | exact resolve eq663 eq117404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117479 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75612 x y
       have i₂ := eq117404
       grind)
    | exact superpose eq117404 eq75612
    | exact resolve eq75612 eq117404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75612
  have eq117482 : y ≠ (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109403 x y
       have i₂ := eq117404
       grind)
    | exact superpose eq117404 eq109403
    | exact resolve eq109403 eq117404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109403 eq117404
  have eq117495 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq117434
  have eq117501 : y ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq117482
       have r₂ := eq12 x y
       grind)
    | exact resolve eq117482 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117482
  have eq117503 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq117479
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq117479
       have r₂ := eq12 x y
       grind)
    | exact resolve eq117479 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117479
  have eq118252 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq109034 (σ x) (σ y)
       have i₂ := eq117503
       grind)
    | exact superpose eq117503 eq109034
    | exact resolve eq109034 eq117503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109034 eq117503
  have eq118280 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq118252
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq118252
    | exact resolve eq118252 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118252
  have eq118307 : (σ y) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq118280
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq118280
    | exact resolve eq118280 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118280
  have eq118320 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | exact superpose eq117398 eq118307
    | exact resolve eq118307 eq117398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118307
  have eq118327 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq117398 eq118320
    | exact resolve eq118320 eq117398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117398 eq118320
  have eq118329 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq118327
       have r₂ := eq16
       grind)
    | exact resolve eq118327 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118327
  have eq118335 : (M.op x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq118329
       grind)
    | exact superpose eq118329 eq10
    | exact resolve eq10 eq118329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118329
  have eq118540 : y = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq118335
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq118335
    | exact resolve eq118335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118335
  have eq118541 : y = (k x y) := by
    first
    | (have r₁ := eq118540
       have r₂ := eq117501
       grind)
    | exact resolve eq118540 eq117501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117501 eq118540
  have eq118542 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117495
       have i₂ := eq118541
       grind)
    | exact superpose eq118541 eq117495
    | exact resolve eq117495 eq118541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117495
  have eq118564 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63 y x
       have i₂ := eq118542
       grind)
    | exact superpose eq118542 eq63
    | exact resolve eq63 eq118542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118631 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq119089 : x = (M.op x (M.op y y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117423 x
       have i₂ := eq118542
       grind)
    | exact superpose eq118542 eq117423
    | exact resolve eq117423 eq118542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117423 eq118542
  have eq119252 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq119089
       have r₂ := eq118631
       grind)
    | exact resolve eq119089 eq118631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118631 eq119089
  have eq119259 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118564 eq119252
    | exact resolve eq119252 eq118564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118564 eq119252
  have eq119260 : x = (M.op x y) := by grind
  clear eq119259
  have eq119265 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq119260
       grind)
    | exact superpose eq119260 eq16
    | exact resolve eq16 eq119260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119304 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7133 y x
       have i₂ := eq119260
       grind)
    | exact superpose eq119260 eq7133
    | exact resolve eq7133 eq119260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7133 eq119260
  have eq119350 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq119265
       have r₂ := eq119304
       grind)
    | exact resolve eq119265 eq119304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119304
  have eq119372 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) (M.op X0 (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq119350
       grind)
    | exact superpose eq119350 eq9
    | exact resolve eq9 eq119350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119383 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq663 (σ y) (σ x)
       have i₂ := eq119350
       grind)
    | exact superpose eq119350 eq663
    | exact resolve eq663 eq119350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq119350
  have eq119464 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq119383
       have r₂ := eq119265
       grind)
    | exact resolve eq119383 eq119265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119383
  have eq119488 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq119464
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq119464
    | exact resolve eq119464 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119464
  have eq119506 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq119488
       have i₂ := eq118541
       grind)
    | exact superpose eq118541 eq119488
    | exact resolve eq119488 eq118541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118541 eq119488
  have eq119559 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq63 (σ y) (σ x)
       have i₂ := eq119506
       grind)
    | exact superpose eq119506 eq63
    | exact resolve eq63 eq119506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq119506
  have eq121635 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq119372 (σ y)
       have i₂ := eq119559
       grind)
    | exact superpose eq119559 eq119372
    | exact resolve eq119372 eq119559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119372
  have eq121808 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121635
       have i₂ := eq119559
       grind)
    | exact superpose eq119559 eq121635
    | exact resolve eq121635 eq119559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119559 eq121635
  have eq121827 : False := by grind
  exact eq121827

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pyx_pxy_Equation450 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law450 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  clear eq18
  have eq63 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X1
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X1)
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X0)
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq74 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 (σ X0))
       have i₂ := eq71 X1 (σ X0)
       grind)
    | exact superpose eq71 eq28
    | exact resolve eq28 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq71
  have eq77 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74
    | exact resolve eq74 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq662 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X1
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X1 X0) X0
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) X1) ∨ (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq662 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq675 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq692 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (M.op X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (τ (M.op X1 (σ X0))) = (M.op (τ (M.op X1 (σ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq14 X0 (τ (M.op X1 (σ X0)))
       grind)
    | exact superpose eq14 eq77
    | (have j1 := eq14 X0 (τ (M.op X1 (σ X0)))
       grind)
    | exact resolve eq77 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : ∀ X0 X1 : G, (τ (M.op X1 (σ X0))) = (M.op (τ (M.op X1 (σ X0))) X0) ∨ (M.op X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq692 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq1356 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq675 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq675
    | (have j0 := eq675 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq675 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42730 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1356 x y
       grind)
    | exact superpose eq1356 eq16
    | (have j1 := eq1356 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1356 x y
       grind)
    | exact resolve eq16 eq1356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356
  have eq42818 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq42730
  have eq101989 : x = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq77 x (σ y)
       have i₂ := eq42818
       grind)
    | exact superpose eq42818 eq77
    | exact resolve eq77 eq42818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42818
  have eq102085 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq101989
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq101989
    | exact resolve eq101989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101989
  have eq102108 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq102085
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq102085
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq102085
       have r₂ := eq12 x y
       grind)
    | exact resolve eq102085 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102085
  have eq102147 : y = (k y (τ (σ x))) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77 y (σ x)
       have i₂ := eq102108
       grind)
    | exact superpose eq102108 eq77
    | exact resolve eq77 eq102108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102148 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ y = (M.op y (τ (σ x))) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq715 y (σ x)
       have i₂ := eq102108
       grind)
    | exact superpose eq102108 eq715
    | exact resolve eq715 eq102108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715 eq102108
  have eq102238 : x = (M.op x y) ∨ y = (M.op y (τ (σ x))) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102148
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq102148
    | exact resolve eq102148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102148
  have eq102239 : x = (M.op x y) ∨ y = (M.op y (τ (σ x))) ∨ x = (k x y) := by grind
  clear eq102238
  have eq102240 : y = (k y x) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102147
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq102147
    | exact resolve eq102147 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102147
  have eq102257 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq102239
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq102239
    | exact resolve eq102239 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102239
  have eq102258 : y = (k y x) ∨ x = (k x y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq102240
       have r₂ := eq12 y x
       grind)
    | exact resolve eq102240 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102240
  have eq102270 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq102257
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq102257
       have r₂ := eq12 y x
       grind)
    | exact resolve eq102257 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102257
  have eq102295 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq675 y x
       have i₂ := eq102258
       grind)
    | exact superpose eq102258 eq675
    | (have j0 := eq675 y x
       grind)
    | exact resolve eq675 eq102258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102258
  have eq102296 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq102295
  have eq102302 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq102270
       grind)
    | exact superpose eq102270 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq102270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102305 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq102302
  have eq102307 : ∀ X0 : G, x = (M.op x (M.op y (M.op X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq102305
       grind)
    | exact superpose eq102305 eq9
    | exact resolve eq9 eq102305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102318 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq663 y x
       have i₂ := eq102305
       grind)
    | exact superpose eq102305 eq663
    | exact resolve eq663 eq102305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102305
  have eq102370 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq102318
  have eq103951 : x = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq77 x (σ y)
       have i₂ := eq102296
       grind)
    | exact superpose eq102296 eq77
    | exact resolve eq77 eq102296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102296
  have eq104047 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq103951
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq103951
    | exact resolve eq103951 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103951
  have eq104048 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq104047
  have eq104096 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq104048
       grind)
    | exact superpose eq104048 eq16
    | exact resolve eq16 eq104048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104048
  have eq104194 : (σ x) ≠ (σ x) ∨ x = (k x y) := by
    first
    | exact superpose eq102270 eq104096
    | exact resolve eq104096 eq102270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102270 eq104096
  have eq104195 : x = (k x y) := by grind
  clear eq104194
  have eq104246 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq675 x y
       have i₂ := eq104195
       grind)
    | exact superpose eq104195 eq675
    | (have j0 := eq675 x y
       grind)
    | exact resolve eq675 eq104195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq104195
  have eq104247 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq104246
  have eq104604 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq663 (σ y) (σ x)
       have i₂ := eq104247
       grind)
    | exact superpose eq104247 eq663
    | exact resolve eq663 eq104247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104657 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq104604
  have eq104673 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104657
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq104657
    | exact resolve eq104657 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104657
  have eq104717 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104673
       have i₂ := eq102370
       grind)
    | exact superpose eq102370 eq104673
    | exact resolve eq104673 eq102370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104673
  have eq104865 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq104717
       have r₂ := eq16
       grind)
    | exact resolve eq104717 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104717
  have eq104870 : y = (k y (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77 y (σ x)
       have i₂ := eq104865
       grind)
    | exact superpose eq104865 eq77
    | exact resolve eq77 eq104865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq104865
  have eq104965 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104870
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq104870
    | exact resolve eq104870 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104870
  have eq104988 : y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq104965
       have r₂ := eq12 y x
       grind)
    | exact resolve eq104965 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104965
  have eq105033 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102370
       have i₂ := eq104988
       grind)
    | exact superpose eq104988 eq102370
    | exact resolve eq102370 eq104988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102370
  have eq105057 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63 y x
       have i₂ := eq105033
       grind)
    | exact superpose eq105033 eq63
    | exact resolve eq63 eq105033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105033
  have eq105127 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102307 y
       have i₂ := eq105057
       grind)
    | exact superpose eq105057 eq102307
    | exact resolve eq102307 eq105057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102307
  have eq105202 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq105127
  have eq105229 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105057 eq105202
    | exact resolve eq105202 eq105057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105057 eq105202
  have eq105230 : x = (M.op x y) := by grind
  clear eq105229
  have eq105248 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq105230
       grind)
    | exact superpose eq105230 eq16
    | exact resolve eq16 eq105230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105230
  have eq105324 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq105248
       have r₂ := eq104247
       grind)
    | exact resolve eq105248 eq104247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104247
  have eq105344 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) (M.op X0 (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq105324
       grind)
    | exact superpose eq105324 eq9
    | exact resolve eq9 eq105324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105355 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq663 (σ y) (σ x)
       have i₂ := eq105324
       grind)
    | exact superpose eq105324 eq663
    | exact resolve eq663 eq105324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq105324
  have eq105420 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq105355
       have r₂ := eq105248
       grind)
    | exact resolve eq105355 eq105248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105355
  have eq105442 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq105420
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq105420
    | exact resolve eq105420 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105420
  have eq105458 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq105442
       have i₂ := eq104988
       grind)
    | exact superpose eq104988 eq105442
    | exact resolve eq105442 eq104988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104988 eq105442
  have eq105509 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq63 (σ y) (σ x)
       have i₂ := eq105458
       grind)
    | exact superpose eq105458 eq63
    | exact resolve eq63 eq105458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq105458
  have eq108685 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq105344 (σ y)
       have i₂ := eq105509
       grind)
    | exact superpose eq105509 eq105344
    | exact resolve eq105344 eq105509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105344
  have eq108855 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq108685
       have i₂ := eq105509
       grind)
    | exact superpose eq105509 eq108685
    | exact resolve eq108685 eq105509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105509 eq108685
  have eq108872 : False := by grind
  exact eq108872

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation450 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law450 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X1
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq18
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq13
    | (have j0 := eq13 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq21 X0 X1
       grind)
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq76 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq48 X0 X1
       grind)
    | exact superpose eq48 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       have j1 := eq48 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq12 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq367 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq366 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq447 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq76
    | (have j0 := eq76 X1 X1
       grind)
    | exact resolve eq76 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq480 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq447
    | (have j0 := eq447 X1 X1
       grind)
    | exact resolve eq447 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq826 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq480 X2 X0
       grind)
    | exact superpose eq480 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq480 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq480 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq480 X0 X0
       grind)
    | exact resolve eq12 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq842 : ∀ X0 X1 X2 : G, (σ (k X2 X0)) = (σ (M.op X0 X2)) ∨ (M.op X0 X2) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq826 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq7804 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X0) ∨ (M.op (M.op X1 X0) X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq367 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq7810 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7804 X0 X1
       grind)
    | (have r₁ := eq7804 X0 X1
       have r₂ := eq21 X0 X1
       grind)
    | exact resolve eq7804 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7804
  have eq7827 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7810 X0 X1
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq7810
    | exact resolve eq7810 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq7810
  have eq7882 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (M.op X0 (σ X1))
       have i₂ := eq7827 (σ X1) X0
       grind)
    | exact superpose eq7827 eq35
    | exact resolve eq35 eq7827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq7883 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k X1 (σ (M.op X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (M.op X0 (τ X1))
       have i₂ := eq7827 (τ X1) X0
       grind)
    | exact superpose eq7827 eq17
    | exact resolve eq17 eq7827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7827
  have eq42464 : ∀ X0 X1 X2 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq842 X0 X2 X1
       grind)
    | exact superpose eq842 eq10
    | (have j1 := eq842 X0 X2 X1
       grind)
    | exact resolve eq10 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq42585 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42464 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq42464
    | (have j0 := eq42464 X0 X1 X1
       grind)
    | exact resolve eq42464 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42464
  have eq43446 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42585 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42585
  have eq43447 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43446 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43446
  have eq43803 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ (M.op X0 (τ X1))) X1) ∨ (σ (M.op X0 (τ X1))) = (M.op (σ (M.op X0 (τ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7883 X0 X1
       have i₂ := eq43447 X1 (σ (M.op X0 (τ X1)))
       grind)
    | exact superpose eq43447 eq7883
    | (have j1 := eq43447 X1 (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq7883 eq43447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7883
  have eq43822 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (M.op (τ (M.op X0 (σ X1))) X1) ∨ (τ (M.op X0 (σ X1))) = (M.op (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7882 X0 X1
       have i₂ := eq43447 X1 (τ (M.op X0 (σ X1)))
       grind)
    | exact superpose eq43447 eq7882
    | (have j1 := eq43447 X1 (τ (M.op X0 (σ X1)))
       grind)
    | exact resolve eq7882 eq43447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7882
  have eq43873 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq43447 (σ X1) (σ X0)
       grind)
    | exact superpose eq43447 eq15
    | (have j1 := eq43447 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq43447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43898 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq43447 (τ X1) X0
       grind)
    | exact superpose eq43447 eq17
    | (have j1 := eq43447 (τ X1) X0
       grind)
    | exact resolve eq17 eq43447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq43447
  have eq44054 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (M.op (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have j0 := eq43822 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43822
  have eq44056 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ (M.op X0 (τ X1))) X1) := by
    intro X0 X1
    first
    | (have j0 := eq43803 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43803
  have eq46029 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq44056 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44056
    | exact resolve eq44056 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44056
  have eq65833 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43898 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq43898
    | exact resolve eq43898 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43898
  have eq66101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65833 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq65833
    | (have j0 := eq65833 X0 X1
       grind)
    | exact resolve eq65833 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65833
  have eq175372 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43873 x y
       grind)
    | exact superpose eq43873 eq16
    | (have j1 := eq43873 x y
       grind)
    | exact resolve eq16 eq43873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43873
  have eq180596 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq175372
       have i₂ := eq66101 y x
       grind)
    | exact superpose eq66101 eq175372
    | (have j1 := eq66101 (σ y) (σ x)
       grind)
    | (have r₁ := eq175372
       have r₂ := eq66101 y x
       grind)
    | exact resolve eq175372 eq66101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66101 eq175372
  have eq180599 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq180596
  have eq181230 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46029 y x
       have i₂ := eq180599
       grind)
    | exact superpose eq180599 eq46029
    | exact resolve eq46029 eq180599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46029 eq180599
  have eq181267 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq181230
  have eq181272 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq181267
       grind)
    | exact superpose eq181267 eq16
    | exact resolve eq16 eq181267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181294 : (τ (σ x)) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq44054 (σ x) y
       have i₂ := eq181267
       grind)
    | exact superpose eq181267 eq44054
    | exact resolve eq44054 eq181267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44054 eq181267
  have eq181502 : x = (M.op x y) := by
    first
    | (have i₁ := eq181294
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq181294
    | exact resolve eq181294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181294
  have eq183204 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq181272
       have i₂ := eq181502
       grind)
    | exact superpose eq181502 eq181272
    | exact resolve eq181272 eq181502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181272 eq181502
  have eq183209 : False := by grind
  exact eq183209

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pyx_Equation450 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law450 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X0)))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq111 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X1
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq111 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq111
    | exact resolve eq111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq178 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq185 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq178
    | (have j0 := eq178 X0 X1
       grind)
    | exact resolve eq178 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1753 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq177
    | exact resolve eq177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1816 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1753 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1753
    | (have j0 := eq1753 X0 X1
       grind)
    | exact resolve eq1753 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq2584 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq185 x y
       grind)
    | exact superpose eq185 eq16
    | (have j1 := eq185 x y
       grind)
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq7511 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2584
       have i₂ := eq1816 x y
       grind)
    | exact superpose eq1816 eq2584
    | (have j1 := eq1816 x y
       grind)
    | (have r₁ := eq2584
       have r₂ := eq1816 x y
       grind)
    | (have r₁ := eq2584
       have r₂ := eq1816 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2584
       have r₂ := eq1816 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2584 eq1816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816 eq2584
  have eq7512 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq7511
  have eq7514 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7512
       grind)
    | exact superpose eq7512 eq16
    | exact resolve eq16 eq7512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7512
  have eq7515 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq7514
       have r₂ := eq23 x
       grind)
    | exact resolve eq7514 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7514
  have eq7517 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7515
       grind)
    | exact superpose eq7515 eq10
    | exact resolve eq10 eq7515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7515
  have eq7569 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq7517
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7517
    | exact resolve eq7517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7517
  have eq7571 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7569
       grind)
    | exact superpose eq7569 eq16
    | exact resolve eq16 eq7569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7569
  have eq7572 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq7571
       have r₂ := eq23 x
       grind)
    | exact resolve eq7571 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq7571
  have eq7589 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq7572
       grind)
    | exact superpose eq7572 eq10
    | exact resolve eq10 eq7572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7572
  have eq7641 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq7589
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7589
    | exact resolve eq7589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7589
  have eq7642 : x = (M.op y y) := by grind
  clear eq7641
  have eq7654 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq114 y
       have i₂ := eq7642
       grind)
    | exact superpose eq7642 eq114
    | exact resolve eq114 eq7642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq7695 : x = (M.op x y) := by
    first
    | (have i₁ := eq111 y y
       have i₂ := eq7642
       grind)
    | exact superpose eq7642 eq111
    | exact resolve eq111 eq7642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq7642
  have eq7727 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7654
       grind)
    | exact superpose eq7654 eq16
    | exact resolve eq16 eq7654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7654
  have eq7740 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq7727
       have i₂ := eq7695
       grind)
    | exact superpose eq7695 eq7727
    | exact resolve eq7727 eq7695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7695 eq7727
  have eq7741 : False := by grind
  exact eq7741

/-- `Equation4502`: `x ◇ (y ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_y_pyx_Equation4502 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4502 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4502.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) X1) := by
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
  have eq57 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ X3 ∨ (M.op (M.op X2 X2) (M.op X2 X2)) = (k (M.op X2 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X2 X2) X3
       have i₂ := eq14 X3 X2 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X2 X2) X3
       grind)
    | (have r₁ := eq13 (M.op X1 X1) (M.op (M.op X2 X3) X1)
       have r₂ := eq14 (M.op (M.op X2 X3) X1) X1 X2 X3
       grind)
    | (have r₁ := eq13 X1 (M.op X0 (M.op X1 X1))
       have r₂ := eq14 X0 X1 X0 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq80 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq84 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq103
    | exact resolve eq103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq110 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq16
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq160 : (σ (k (k y y) x)) = (k (k (σ y) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq40 (k y y)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq40
    | exact resolve eq40 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq217 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 x X2
       have i₂ := eq14 x X2 X0 X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, (M.op (M.op x y) X0) = (k (M.op X0 X0) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq118 (M.op x x)
       have i₂ := eq56 (M.op x x) x
       grind)
    | exact superpose eq56 eq118
    | exact resolve eq118 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op (M.op X2 X3) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X2 X3
       have i₂ := eq56 (M.op X0 X0) X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq221 X0 X1 x x
       have i₂ := eq56 (M.op x x) X0
       grind)
    | exact superpose eq56 eq221
    | exact resolve eq221 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq231 : ∀ X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X1
    first
    | (have i₁ := eq57 x X1
       have i₂ := eq56 x X1
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq767 : ∀ X2 X3 : G, (M.op (M.op x y) X2) ≠ X3 ∨ (M.op (M.op X2 X2) (M.op X2 X2)) = (k (M.op X2 X2) X3) := by
    intro X2 X3
    first
    | (have i₁ := eq69 x x X2 X3
       have i₂ := eq217 x x X2
       grind)
    | (have i₁ := eq69 x y X2 X3
       have i₂ := eq217 x x X2
       grind)
    | exact superpose eq217 eq69
    | (have j0 := eq69 x y X2 X3
       grind)
    | (have r₁ := eq69 x x X2 (M.op (M.op x y) X2)
       have r₂ := eq217 x x X2
       grind)
    | (have r₁ := eq69 x y X2 (M.op (M.op x x) X2)
       have r₂ := eq217 x x X2
       grind)
    | exact resolve eq69 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq768 : ∀ X2 X3 : G, (M.op (M.op x y) X2) ≠ X3 ∨ (k (M.op X2 X2) X3) = (M.op (M.op x y) X2) := by
    intro X2 X3
    first
    | (have i₁ := eq767 X2 X3
       have i₂ := eq56 (M.op X2 X2) X2
       grind)
    | exact superpose eq56 eq767
    | (have j0 := eq767 X2 X3
       grind)
    | (have r₁ := eq767 (M.op x x) (M.op (M.op x y) x)
       have r₂ := eq56 (M.op x y) x
       grind)
    | (have r₁ := eq767 x (M.op x (M.op x x))
       have r₂ := eq56 x x
       grind)
    | exact resolve eq767 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq925 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq82 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq935 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq925 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq925 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq925 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq925 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq946 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq935 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq935
    | (have j0 := eq935 X0 X1
       grind)
    | exact resolve eq935 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq3721 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq84 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq84
    | (have j0 := eq84 y
       grind)
    | exact resolve eq84 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq3728 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3721
  have eq3732 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3728
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq3728
    | exact resolve eq3728 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728
  have eq3756 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3732
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq3732 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3732
  have eq3788 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3756 eq110
    | exact resolve eq110 eq3756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq4317 : (σ (k (k y y) x)) = (M.op (σ x) (k (σ y) (σ y))) ∨ (σ x) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq167 (k y y)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq167
    | exact resolve eq167 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq167
  have eq4358 : (σ (k (k y y) x)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | exact superpose eq3756 eq4317
    | exact resolve eq4317 eq3756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4317
  have eq4389 : (σ (k (k y y) x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq4358
       have i₂ := eq56 sF2 sF3
       grind)
    | exact superpose eq56 eq4358
    | exact resolve eq4358 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4358
  have eq4413 : (k (k (σ y) (σ y)) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq4389
       have i₂ := eq160
       grind)
    | exact superpose eq160 eq4389
    | exact resolve eq4389 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq4389
  have eq4432 : (M.op (M.op x y) (σ y)) = (k (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | exact superpose eq3756 eq4413
    | exact resolve eq4413 eq3756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4413
  have eq4438 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (M.op (M.op x y) (σ y)) = (k (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | exact superpose eq3756 eq4432
    | exact resolve eq4432 eq3756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4432
  have eq4444 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (M.op (M.op x y) (σ y)) = (k (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq4438
       have i₂ := eq56 (M.op sF3 sF3) sF3
       grind)
    | exact superpose eq56 eq4438
    | exact resolve eq4438 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4438
  have eq4450 : (M.op (M.op x y) (σ y)) = (k (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | (have j1 := eq768 (σ y) (σ x)
       grind)
    | (have r₁ := eq4444
       have r₂ := eq768 (σ y) (σ x)
       grind)
    | (have r₁ := eq4444
       have r₂ := eq768 (σ y) (k (M.op (σ y) (σ y)) (σ x))
       grind)
    | exact resolve eq4444 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4444
  have eq4456 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (M.op (M.op x y) (σ y)) = (k (M.op (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq3756 eq4450
    | exact resolve eq4450 eq3756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3756 eq4450
  have eq4462 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (M.op (M.op x y) (σ y)) = (k (M.op (σ y) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq4456
       have i₂ := eq56 sF2 sF3
       grind)
    | exact superpose eq56 eq4456
    | exact resolve eq4456 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4456
  have eq4468 : (M.op (M.op x y) (σ y)) = (k (M.op (σ y) (σ y)) (σ x)) := by
    first
    | (have j1 := eq768 (σ y) (σ x)
       grind)
    | (have r₁ := eq4462
       have r₂ := eq768 (σ y) (σ x)
       grind)
    | (have r₁ := eq4462
       have r₂ := eq768 (σ y) (k (M.op (σ y) (σ y)) (σ x))
       grind)
    | exact resolve eq4462 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq4462
  have eq6422 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq946 X0 (M.op X0 X0)
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq946
    | (have j0 := eq946 X0 (M.op X0 X0)
       grind)
    | exact resolve eq946 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq946
  have eq6561 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6422 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6422
  have eq6562 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6561 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6561
  have eq7088 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6562 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6562
    | (have j0 := eq6562 x
       grind)
    | exact resolve eq6562 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7089 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq6562 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6562
    | (have j0 := eq6562 y
       grind)
    | exact resolve eq6562 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq7102 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq217 (σ X0) (σ X0) X1
       have i₂ := eq6562 X0
       grind)
    | exact superpose eq6562 eq217
    | exact resolve eq217 eq6562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7201 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq6562 (M.op x x)
       have i₂ := eq7088
       grind)
    | exact superpose eq7088 eq6562
    | exact resolve eq6562 eq7088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7088
  have eq7202 : (σ (M.op (M.op x y) x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq7201
       have i₂ := eq56 (M.op x x) x
       grind)
    | exact superpose eq56 eq7201
    | exact resolve eq7201 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7201
  have eq7215 : (σ (M.op (M.op x y) x)) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq7202
       have i₂ := eq56 (M.op sF2 sF2) sF2
       grind)
    | exact superpose eq56 eq7202
    | exact resolve eq7202 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7202
  have eq7276 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq7089
       grind)
    | exact superpose eq7089 eq16
    | exact resolve eq16 eq7089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7300 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq6562 (M.op y y)
       have i₂ := eq7089
       grind)
    | exact superpose eq7089 eq6562
    | exact resolve eq6562 eq7089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6562 eq7089
  have eq7301 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq7300
       have i₂ := eq56 (M.op y y) y
       grind)
    | exact superpose eq56 eq7300
    | exact resolve eq7300 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7300
  have eq7313 : (M.op y y) = (k y y) := by
    first
    | exact superpose eq3788 eq7276
    | exact resolve eq7276 eq3788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7276
  have eq7314 : (σ (M.op (M.op x y) y)) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq7301
       have i₂ := eq56 (M.op sF3 sF3) sF3
       grind)
    | exact superpose eq56 eq7301
    | exact resolve eq7301 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq7301
  have eq7981 : (M.op (M.op x y) x) = (τ (M.op (M.op x y) (σ x))) := by
    first
    | exact superpose eq7215 eq16
    | exact resolve eq16 eq7215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7215
  have eq8038 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) (σ y))) := by
    first
    | exact superpose eq7314 eq16
    | exact resolve eq16 eq7314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14931 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq14932 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq14931
    | exact resolve eq14931 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14931
  have eq14943 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq14932
       have r₂ := eq28
       grind)
    | exact resolve eq14932 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14932
  have eq14947 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq14943
    | exact resolve eq14943 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14943
  have eq14952 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14947 eq3788
    | exact resolve eq3788 eq14947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3788 eq14947
  have eq14965 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14952
       have i₂ := eq7313
       grind)
    | exact superpose eq7313 eq14952
    | exact resolve eq14952 eq7313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7313 eq14952
  have eq14967 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq14965
    | exact resolve eq14965 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14965
  have eq14968 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14967
  have eq14976 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7102 y X0
       have i₂ := eq14968
       grind)
    | exact superpose eq14968 eq7102
    | exact resolve eq7102 eq14968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7102
  have eq14981 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq217 y y X0
       have i₂ := eq14968
       grind)
    | exact superpose eq14968 eq217
    | exact resolve eq217 eq14968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14968
  have eq14987 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14976 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14976
    | (have j0 := eq14976 X0
       grind)
    | exact resolve eq14976 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14976
  have eq15164 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14981 eq7314
    | exact resolve eq7314 eq14981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14981
  have eq15199 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15164
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15164
    | exact resolve eq15164 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15164
  have eq15204 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq15199
    | exact resolve eq15199 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15199
  have eq17106 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq14987
    | (have j0 := eq14987 (σ y)
       grind)
    | exact resolve eq14987 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14987
  have eq17165 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17106 eq15204
    | exact resolve eq15204 eq17106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15204 eq17106
  have eq17183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17165
  have eq17187 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17183
       have r₂ := eq28
       grind)
    | exact resolve eq17183 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17183
  have eq17191 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17187 eq231
    | exact resolve eq231 eq17187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq17201 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17191
    | (have j0 := eq17191 (σ y)
       grind)
    | exact resolve eq17191 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17191
  have eq17261 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17201 eq220
    | exact resolve eq220 eq17201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq17262 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17201 eq227
    | exact resolve eq227 eq17201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq17201
  have eq17282 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17187 eq17262
    | exact resolve eq17262 eq17187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17262
  have eq17331 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17282 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17282
  have eq17412 : (τ (σ x)) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17331 eq7981
    | exact resolve eq7981 eq17331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7981 eq17331
  have eq17448 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq17412
    | exact resolve eq17412 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17412
  have eq17474 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17448 eq217
    | exact resolve eq217 eq17448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17448
  have eq17770 : (σ x) = (k (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17187 eq17261
    | exact resolve eq17261 eq17187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17187 eq17261
  have eq17782 : (σ x) = (k (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq17770
  have eq17791 : (σ x) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4468 eq17782
    | exact resolve eq17782 eq4468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4468 eq17782
  have eq17807 : (τ (σ x)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17791 eq8038
    | exact resolve eq8038 eq17791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8038 eq17791
  have eq17834 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq17807
    | exact resolve eq17807 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17807
  have eq19694 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17474 eq17834
    | exact resolve eq17834 eq17474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17474 eq17834
  have eq19779 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19694
  have eq19807 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19779
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19779
    | exact resolve eq19779 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19779
  have eq19808 : x = (M.op x y) := by grind
  clear eq19807
  have eq19815 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq19808 eq21
    | exact resolve eq21 eq19808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19884 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq19808 eq7314
    | exact resolve eq7314 eq19808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7314
  have eq19915 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq19884
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19884
    | exact resolve eq19884 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq19884
  have eq19972 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19815
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19815
    | exact resolve eq19815 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq19815
  have eq19977 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq21 eq19915
    | exact resolve eq19915 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq19915
  have eq20087 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq19972 eq27
    | exact resolve eq27 eq19972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19972
  have eq20280 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq19977 eq217
    | exact resolve eq217 eq19977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq20284 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq19808 eq20280
    | exact resolve eq20280 eq19808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19808 eq20280
  have eq20879 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq20284 eq20087
    | exact resolve eq20087 eq20284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20087 eq20284
  have eq20913 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19977 eq20879
    | exact resolve eq20879 eq19977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19977 eq20879
  have eq20922 : False := by grind
  exact eq20922

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_y_pyx_x_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
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
  clear eq43
  have eq51 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 x x X4 X5
       have i₂ := eq14 x x X0 X1
       grind)
    | (have i₁ := eq14 (M.op x (M.op X1 X1)) X1 x x
       have i₂ := eq14 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | (have i₁ := eq14 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq97 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq97 y x
       grind)
    | exact superpose eq97 eq75
    | (have j1 := eq97 y x
       grind)
    | exact resolve eq75 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq120
    | exact resolve eq120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq123 eq97
    | (have j0 := eq97 (σ y) (σ x)
       grind)
    | exact resolve eq97 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq126
    | exact resolve eq126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq130 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq127
       have r₂ := eq27
       grind)
    | exact resolve eq127 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq132 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq130
    | exact resolve eq130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq142 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq173 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq97 (σ X0) sF2
       grind)
    | exact superpose eq97 eq39
    | (have j1 := eq97 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq223 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq55 X0 (M.op x x)
       have i₂ := eq55 (M.op x x) x
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | (have i₁ := eq55 (M.op x (M.op X1 X1)) X1
       have i₂ := eq14 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
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
  have eq237 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq132 eq236
    | exact resolve eq236 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq241 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq237
    | exact resolve eq237 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq243 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq241 eq14
    | exact resolve eq14 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq243 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq243
    | exact resolve eq243 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq316 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ y)) y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq241 eq51
    | exact resolve eq51 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq368 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq244 eq316
    | exact resolve eq316 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq316
  have eq383 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) y) ∨ x = (M.op x y) := by grind
  clear eq368
  have eq405 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq241 eq383
    | exact resolve eq383 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq423 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) y) ∨ x = (M.op x y) := by grind
  clear eq405
  have eq424 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq132 eq423
    | exact resolve eq423 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq436 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by grind
  clear eq424
  have eq569 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op x y) y) X5) := by
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
  have eq570 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X5) := by
    intro X5
    first
    | (have i₁ := eq569 x x X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq569
    | exact resolve eq569 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq569
  have eq586 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq241 eq570
    | exact resolve eq570 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op X0 (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq570 eq13
    | (have j0 := eq13 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) y) x
       have r₂ := eq570 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op X0 X0) = X0 ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq570 eq12
    | (have j0 := eq12 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq12 x (M.op (M.op x y) y)
       have r₂ := eq570 x
       grind)
    | exact resolve eq12 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq605 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq613 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq601 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq620 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq132 eq586
    | exact resolve eq586 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq650 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq620 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq656 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 X1) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq650 (M.op X1 X1)
       have i₂ := eq14 sF2 X1 x x
       grind)
    | exact superpose eq14 eq650
    | exact resolve eq650 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq8306 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq223 eq613
    | exact resolve eq613 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq613
  have eq8310 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq241 eq8306
    | exact resolve eq8306 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq8315 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq132 eq8310
    | exact resolve eq8310 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq8310
  have eq8328 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8315 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8315
  have eq8340 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8328 eq49
    | exact resolve eq49 eq8328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq8328
  have eq8347 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq8340
    | exact resolve eq8340 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq8340
  have eq8357 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq97 x x
       have i₂ := eq8347
       grind)
    | exact superpose eq8347 eq97
    | (have j0 := eq97 x x
       grind)
    | exact resolve eq97 eq8347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8347
  have eq8358 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq8357
  have eq8387 : (σ x) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq656 x x
       have i₂ := eq8358
       grind)
    | exact superpose eq8358 eq656
    | exact resolve eq656 eq8358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq8390 : (σ x) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq8387
  have eq8399 : x = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8358
       have i₂ := eq8390
       grind)
    | exact superpose eq8390 eq8358
    | exact resolve eq8358 eq8390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8358 eq8390
  have eq8417 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq8399
  have eq8439 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8417 eq436
    | exact resolve eq436 eq8417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq8417
  have eq8500 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8439
  have eq8512 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8500
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8500
    | exact resolve eq8500 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8500
  have eq8513 : x = (M.op x y) := by grind
  clear eq8512
  have eq8516 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq8513 eq20
    | exact resolve eq20 eq8513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8524 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq8513 eq570
    | exact resolve eq570 eq8513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq8526 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq8513 eq8306
    | exact resolve eq8306 eq8513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8306
  have eq8528 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq8526 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8526
    | (have j0 := eq8526 X0
       grind)
    | exact resolve eq8526 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8526
  have eq8530 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq8524 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8524
    | (have j0 := eq8524 X0
       grind)
    | exact resolve eq8524 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8524
  have eq8537 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq8516
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8516
    | exact resolve eq8516 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8516
  have eq8538 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | exact superpose eq8513 eq8528
    | exact resolve eq8528 eq8513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8528
  have eq8540 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq8513 eq8530
    | exact resolve eq8530 eq8513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8530
  have eq8543 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq8537 eq26
    | exact resolve eq26 eq8537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq8602 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 x
       have i₂ := eq8538 (τ X0)
       grind)
    | exact superpose eq8538 eq38
    | exact resolve eq38 eq8538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq8538
  have eq8609 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq8602 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8602
    | (have j0 := eq8602 X0
       grind)
    | exact resolve eq8602 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8602
  have eq8613 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq8537 eq8609
    | exact resolve eq8609 eq8537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8609
  have eq8875 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq8513 eq612
    | (have j0 := eq612 X0
       grind)
    | exact resolve eq612 eq8513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq8876 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8875 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8875
    | (have j0 := eq8875 X0
       grind)
    | exact resolve eq8875 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8875
  have eq8877 : ∀ X0 : G, (k X0 x) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq8513 eq8876
    | (have j0 := eq8876 X0
       grind)
    | exact resolve eq8876 eq8513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8876
  have eq8946 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq8877 y
       grind)
    | exact superpose eq8877 eq75
    | (have j1 := eq8877 y
       grind)
    | exact resolve eq75 eq8877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq8877
  have eq8958 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8537 eq8946
    | exact resolve eq8946 eq8537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8946
  have eq8960 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8958
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8958
    | exact resolve eq8958 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8958
  have eq9040 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8960 eq97
    | (have j0 := eq97 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq97 eq8960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8960
  have eq9041 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8543 eq9040
    | exact resolve eq9040 eq8543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9040
  have eq9044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8543 eq9041
    | exact resolve eq9041 eq8543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9041
  have eq9047 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9044
       have r₂ := eq27
       grind)
    | exact resolve eq9044 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9044
  have eq9052 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq9047
       grind)
    | exact superpose eq9047 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq9047
       grind)
    | exact resolve eq13 eq9047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9047
  have eq9064 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq9052 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9052
  have eq9556 : (k (σ y) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq9064 sF0
       grind)
    | exact superpose eq9064 eq77
    | exact resolve eq77 eq9064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq9064
  have eq9559 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8513 eq9556
    | exact resolve eq9556 eq8513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9556
  have eq9562 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9559
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9559
    | exact resolve eq9559 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9559
  have eq9564 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9562
    | exact resolve eq9562 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9562
  have eq9570 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9564 eq97
    | (have j0 := eq97 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq97 eq9564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq9564
  have eq9571 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9570
  have eq9573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8543 eq9571
    | exact resolve eq9571 eq8543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9571
  have eq9576 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9573
       have r₂ := eq27
       grind)
    | exact resolve eq9573 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9573
  have eq9581 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq9576 eq27
    | exact resolve eq27 eq9576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq10263 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq8537 eq173
    | (have j0 := eq173 X0
       grind)
    | exact resolve eq173 eq8537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq10264 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq8537 eq10263
    | (have j0 := eq10263 X0
       grind)
    | exact resolve eq10263 eq8537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8537 eq10263
  have eq10285 : (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10264
    | (have j0 := eq10264 (M.op x y)
       grind)
    | exact resolve eq10264 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10264
  have eq10310 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq142 eq10285
    | exact resolve eq10285 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq10285
  have eq10334 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq8613 eq10310
    | exact resolve eq10310 eq8613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8613 eq10310
  have eq10335 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq10334
  have eq10418 : (M.op (M.op x y) y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq10335 eq225
    | exact resolve eq225 eq10335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq10427 : (σ (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq10335 eq10418
    | exact resolve eq10418 eq10335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10335 eq10418
  have eq10436 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq8513 eq10427
    | exact resolve eq10427 eq8513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10427
  have eq10444 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq10436
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10436
    | exact resolve eq10436 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10436
  have eq10452 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq8513 eq10444
    | exact resolve eq10444 eq8513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8513 eq10444
  have eq10468 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq10452 eq8543
    | exact resolve eq8543 eq10452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8543
  have eq10478 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10468
       have i₂ := eq8540 sF3
       grind)
    | exact superpose eq8540 eq10468
    | exact resolve eq10468 eq8540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8540 eq10468
  have eq10489 : x = (σ y) := by
    first
    | exact superpose eq9576 eq10478
    | exact resolve eq10478 eq9576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9576 eq10478
  have eq10529 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq10489 eq9581
    | exact resolve eq9581 eq10489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9581 eq10489
  have eq10534 : False := by grind
  exact eq10534

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pxx_x_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq101 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq78
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq78
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq120
    | exact resolve eq120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq141 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq164 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq141 eq16
    | exact resolve eq16 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq55 X0 (M.op x x)
       have i₂ := eq55 (M.op x x) x
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | (have i₁ := eq55 (M.op x (M.op X1 X1)) X1
       have i₂ := eq14 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
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
  have eq374 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq220 (M.op x X1) X1
       have i₂ := eq220 x X1
       grind)
    | (have i₁ := eq220 (M.op x y) y
       have i₂ := eq220 x X1
       grind)
    | exact superpose eq220 eq220
    | exact resolve eq220 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq374 eq13
    | (have j0 := eq13 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) y) x
       have r₂ := eq374 x
       grind)
    | exact resolve eq13 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 : G, (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq461 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq466 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq218 eq463
    | exact resolve eq463 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq475 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq466 eq38
    | exact resolve eq38 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1204 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq100 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq100 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1206 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1205 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq3702 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq101 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq101
    | (have j0 := eq101 x
       grind)
    | exact resolve eq101 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq3713 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3702
  have eq3721 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3713
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3713
    | exact resolve eq3713 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq3713
  have eq3739 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3721
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq3721 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3721
  have eq3746 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3739 eq49
    | exact resolve eq49 eq3739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3739
  have eq4244 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq142
    | (have j0 := eq142 (M.op x y)
       grind)
    | exact resolve eq142 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq4253 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq4244
  have eq4259 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq141 eq4253
    | exact resolve eq4253 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq4253
  have eq4291 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq4259
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4259 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4259
  have eq4330 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq4291 eq164
    | exact resolve eq164 eq4291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq12875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq122 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12875
    | exact resolve eq12875 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12875
  have eq12893 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq12882
       have r₂ := eq27
       grind)
    | exact resolve eq12882 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12882
  have eq12895 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12893
    | exact resolve eq12893 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12893
  have eq12899 : (M.op (M.op x y) y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12895 eq220
    | exact resolve eq220 eq12895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12901 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12895 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq12895
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq12895
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12895
       grind)
    | exact resolve eq13 eq12895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12903 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq12901
  have eq17790 : (σ y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12899 eq12895
    | exact resolve eq12895 eq12899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12895 eq12899
  have eq17799 : (σ y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq17790
  have eq17806 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq17799 eq218
    | exact resolve eq218 eq17799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17812 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq17799 eq466
    | exact resolve eq466 eq17799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17840 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq17806 eq55
    | exact resolve eq55 eq17806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17806
  have eq18160 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17812 eq122
    | exact resolve eq122 eq17812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17812
  have eq18173 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18160
  have eq22794 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12903 eq122
    | exact resolve eq122 eq12903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq12903
  have eq22828 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22794
  have eq22851 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22828 eq55
    | exact resolve eq55 eq22828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22828
  have eq23831 : ∀ X0 : G, (σ y) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22851 eq17799
    | exact resolve eq17799 eq22851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17799
  have eq23868 : ∀ X0 : G, (σ y) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq23831 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23831
  have eq23904 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq23868 eq4330
    | exact resolve eq4330 eq23868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4330 eq23868
  have eq23919 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq23904
    | exact resolve eq23904 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq23904
  have eq23940 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq23919 eq1204
    | (have j0 := eq1204 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1204 eq23919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204 eq23919
  have eq23949 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq23940
  have eq23956 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq23949
    | exact resolve eq23949 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23949
  have eq23972 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq23956
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23956
    | exact resolve eq23956 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23956
  have eq23985 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq23972
       have r₂ := eq18173
       grind)
    | exact resolve eq23972 eq18173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18173 eq23972
  have eq23992 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq23985
    | exact resolve eq23985 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23985
  have eq24021 : (σ (M.op x y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq23992 eq22851
    | exact resolve eq22851 eq23992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22851 eq23992
  have eq24030 : (σ (M.op x y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24021
  have eq25094 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq17840
    | (have j0 := eq17840 (σ x)
       grind)
    | exact resolve eq17840 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17840
  have eq25216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq25094 eq24030
    | exact resolve eq24030 eq25094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24030 eq25094
  have eq25225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25216
  have eq25242 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq25225
       have r₂ := eq27
       grind)
    | exact resolve eq25225 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25225
  have eq25245 : (M.op (M.op x y) y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq220 y x
       have i₂ := eq25242
       grind)
    | exact superpose eq25242 eq220
    | exact resolve eq220 eq25242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25247 : y ≠ y ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq25242
       grind)
    | exact superpose eq25242 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25242
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25242
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq25242
       grind)
    | exact resolve eq13 eq25242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25249 : (k y x) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25247
  have eq25257 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq25245 eq218
    | exact resolve eq218 eq25245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25446 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq25257 X0
       have i₂ := eq25242
       grind)
    | exact superpose eq25242 eq25257
    | exact resolve eq25257 eq25242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25242 eq25257
  have eq25470 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq25446 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25446
  have eq25498 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq55 X0 y
       have i₂ := eq25470 y
       grind)
    | exact superpose eq25470 eq55
    | exact resolve eq55 eq25470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25522 : ∀ X0 : G, y = (k y X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq466 X0
       have i₂ := eq25470 sF0
       grind)
    | exact superpose eq25470 eq466
    | exact resolve eq466 eq25470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq25523 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq475 X0
       have i₂ := eq25470 sF0
       grind)
    | exact superpose eq25470 eq475
    | exact resolve eq475 eq25470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25470
  have eq25571 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq25523 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25523
    | (have j0 := eq25523 X0
       grind)
    | exact resolve eq25523 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25523
  have eq25697 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1206 y
       have i₂ := eq25522 y
       grind)
    | exact superpose eq25522 eq1206
    | (have j0 := eq1206 y
       grind)
    | exact resolve eq1206 eq25522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206 eq25522
  have eq25796 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25697
  have eq25867 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25796
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25796
    | exact resolve eq25796 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25796
  have eq25907 : ∀ X0 : G, (σ y) = (σ (k y X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq25571
    | exact resolve eq25571 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq25571
  have eq26748 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq25867 eq55
    | exact resolve eq55 eq25867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31100 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25907 x
       have i₂ := eq25249
       grind)
    | exact superpose eq25249 eq25907
    | exact resolve eq25907 eq25249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25249 eq25907
  have eq31227 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31100
  have eq32172 : ∀ X0 : G, (M.op y x) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq25245
       have i₂ := eq25498 sF0
       grind)
    | exact superpose eq25498 eq25245
    | exact resolve eq25245 eq25498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25245 eq25498
  have eq32207 : ∀ X0 : G, (M.op y x) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq32172 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32172
  have eq34855 : (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31227
       have i₂ := eq32207 y
       grind)
    | exact superpose eq32207 eq31227
    | exact resolve eq31227 eq32207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31227
  have eq34907 : (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34855
  have eq34967 : ∀ X0 : G, (σ y) = (σ (M.op X0 y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34907
       have i₂ := eq32207 X0
       grind)
    | exact superpose eq32207 eq34907
    | exact resolve eq34907 eq32207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32207 eq34907
  have eq35038 : ∀ X0 : G, (σ y) = (σ (M.op X0 y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq34967 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34967
  have eq35062 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35038 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35038
    | (have j0 := eq35038 x
       grind)
    | exact resolve eq35038 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35038
  have eq35206 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq35062
    | exact resolve eq35062 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35062
  have eq43991 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq26748
    | (have j0 := eq26748 (σ x)
       grind)
    | exact resolve eq26748 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44076 : (σ y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26748 eq25867
    | exact resolve eq25867 eq26748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25867 eq26748
  have eq44083 : (σ y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq44076
  have eq46004 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44083 eq43991
    | exact resolve eq43991 eq44083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43991 eq44083
  have eq46027 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq46004
  have eq46493 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46027 eq27
    | exact resolve eq27 eq46027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46027
  have eq46540 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq46493
       have r₂ := eq35206
       grind)
    | exact resolve eq46493 eq35206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35206 eq46493
  have eq46545 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46540 eq229
    | exact resolve eq229 eq46540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq46576 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq46545
    | exact resolve eq46545 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46545
  have eq46924 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq46576 eq218
    | exact resolve eq218 eq46576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq46929 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq46576 eq374
    | exact resolve eq374 eq46576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46576
  have eq47029 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq46540 eq46924
    | exact resolve eq46924 eq46540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46924
  have eq47075 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq47029 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47029
  have eq47421 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq46540 eq46929
    | exact resolve eq46929 eq46540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46540 eq46929
  have eq47514 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq47421 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47421
  have eq47963 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq47075 (M.op x sF2)
       have i₂ := eq220 x sF2
       grind)
    | exact superpose eq220 eq47075
    | exact resolve eq47075 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48003 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47075 eq3746
    | exact resolve eq3746 eq47075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3746 eq47075
  have eq48051 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq48003
    | exact resolve eq48003 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq48003
  have eq49332 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq48051
       grind)
    | exact superpose eq48051 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq48051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48051
  have eq49345 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq49332
  have eq51123 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq55 X0 x
       have i₂ := eq49345
       grind)
    | exact superpose eq49345 eq55
    | exact resolve eq55 eq49345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq77731 : ∀ X0 : G, (σ x) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq51123 eq47963
    | exact resolve eq47963 eq51123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47963 eq51123
  have eq77788 : ∀ X0 : G, (σ x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq77731 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77731
  have eq77890 : x = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq49345
       have i₂ := eq77788 x
       grind)
    | exact superpose eq77788 eq49345
    | exact resolve eq49345 eq77788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49345 eq77788
  have eq77940 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq77890
  have eq78126 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq77940 eq47514
    | exact resolve eq47514 eq77940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47514 eq77940
  have eq78163 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq78126 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78126
  have eq80048 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq78163 y
       grind)
    | exact superpose eq78163 eq18
    | (have j1 := eq78163 y
       grind)
    | exact resolve eq18 eq78163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78163
  have eq80126 : x = (M.op x y) := by grind
  clear eq80048
  have eq80161 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq80126 eq20
    | exact resolve eq20 eq80126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80222 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq80126 eq374
    | exact resolve eq374 eq80126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq80225 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq80126 eq475
    | exact resolve eq475 eq80126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq80367 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq80225 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80225
    | (have j0 := eq80225 X0
       grind)
    | exact resolve eq80225 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80225
  have eq80370 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq80222 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80222
    | (have j0 := eq80222 X0
       grind)
    | exact resolve eq80222 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80222
  have eq80427 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq80161
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq80161
    | exact resolve eq80161 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq80161
  have eq80444 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq20 eq80367
    | (have j0 := eq80367 X0
       grind)
    | exact resolve eq80367 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq80367
  have eq80447 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq80126 eq80370
    | exact resolve eq80370 eq80126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80370
  have eq80517 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq80427 eq26
    | exact resolve eq26 eq80427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq80427
  have eq80812 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4291 eq80444
    | exact resolve eq80444 eq4291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4291 eq80444
  have eq82155 : (M.op (M.op x y) y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq80812 eq220
    | exact resolve eq220 eq80812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq82160 : (σ (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq80812 eq82155
    | exact resolve eq82155 eq80812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80812 eq82155
  have eq82171 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq80126 eq82160
    | exact resolve eq82160 eq80126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82160
  have eq82182 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq82171
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82171
    | exact resolve eq82171 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq82171
  have eq82193 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq80126 eq82182
    | exact resolve eq82182 eq80126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80126 eq82182
  have eq82306 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq82193 eq80517
    | exact resolve eq80517 eq82193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80517
  have eq82309 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq82306
       have i₂ := eq80447 sF3
       grind)
    | exact superpose eq80447 eq82306
    | exact resolve eq82306 eq80447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80447 eq82306
  have eq82575 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq82309 eq27
    | exact resolve eq27 eq82309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq82309
  have eq82634 : False := by grind
  exact eq82634

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxx_x_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq85 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq163 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq85 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq85
    | exact resolve eq85 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq178 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | (have i₁ := eq16 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq178 x x X2 X3 X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq184 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq183 x x X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq183
    | exact resolve eq183 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq186 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq180 (M.op X0 X0) X0
       grind)
    | exact superpose eq180 eq186
    | exact resolve eq186 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq188 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq179 X0 (M.op x x)
       have i₂ := eq179 (M.op x x) x
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq179 x x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq179 x x
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq179
    | exact resolve eq179 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq204 eq184
    | exact resolve eq184 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq184 eq187
    | exact resolve eq187 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : (k (σ (M.op x x)) (σ x)) = (σ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq39 (M.op x x)
       have i₂ := eq187 x
       grind)
    | exact superpose eq187 eq39
    | exact resolve eq39 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : (σ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq41 (M.op sF0 sF0)
       have i₂ := eq187 sF0
       grind)
    | exact superpose eq187 eq41
    | exact resolve eq41 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq247 : (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq204 eq246
    | exact resolve eq246 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq249 : (k (σ (M.op x x)) (σ x)) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq204 eq244
    | exact resolve eq244 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq250 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq204 eq243
    | exact resolve eq243 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq336 : (k (τ (M.op (σ x) (σ x))) x) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq187 sF2
       grind)
    | exact superpose eq187 eq141
    | exact resolve eq141 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq357 : (k (τ (M.op (σ x) (σ x))) x) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq204 eq336
    | exact resolve eq336 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq380 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op x y)) := by
    first
    | (have i₁ := eq163 (M.op sF1 sF1)
       have i₂ := eq187 sF1
       grind)
    | exact superpose eq187 eq163
    | exact resolve eq163 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq401 : (τ (M.op (M.op x y) y)) = (k (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op x y)) := by
    first
    | exact superpose eq204 eq380
    | exact resolve eq380 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq454 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq501 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq187 (τ X0)
       grind)
    | exact superpose eq187 eq38
    | exact resolve eq38 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq187
  have eq533 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | exact superpose eq204 eq501
    | exact resolve eq501 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq1150 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq1151 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1197 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1196 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq1688 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1150
       grind)
    | exact superpose eq1150 eq39
    | exact resolve eq39 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq1689 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1688
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1688
    | exact resolve eq1688 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688
  have eq1691 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1689
    | exact resolve eq1689 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq1734 : ∀ X0 : G, (τ (σ (M.op (M.op x y) y))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq454 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq533 (σ X0)
       grind)
    | exact superpose eq533 eq454
    | exact resolve eq454 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq533
  have eq1746 : ∀ X0 : G, (τ (σ (M.op (M.op x y) y))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq1734 X0
       have i₂ := eq15 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq15 eq1734
    | exact resolve eq1734 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq1764 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq1746 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1746
    | exact resolve eq1746 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746
  have eq1782 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1764 X0
       have i₂ := eq15 (M.op sF0 y)
       grind)
    | exact superpose eq15 eq1764
    | exact resolve eq1764 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq1828 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1691 eq1151
    | exact resolve eq1151 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1835 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1828
       have r₂ := eq27
       grind)
    | exact resolve eq1828 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq1843 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1835 eq179
    | exact resolve eq179 eq1835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1849 : (k (σ y) (σ x)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1835 eq1782
    | exact resolve eq1782 eq1835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1865 : (σ (M.op x y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1691 eq1849
    | exact resolve eq1849 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691 eq1849
  have eq1880 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1865 eq188
    | exact resolve eq188 eq1865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1944 : (τ (M.op (M.op x y) y)) = (k (τ (σ (M.op x y))) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1880 eq401
    | exact resolve eq401 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq1880
  have eq1945 : (k (M.op x y) (M.op x y)) = (τ (M.op (M.op x y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq1944
    | exact resolve eq1944 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq1975 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1865 eq1945
    | exact resolve eq1945 eq1865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945
  have eq1991 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq1975
    | exact resolve eq1975 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1975
  have eq2112 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1991 eq1197
    | (have j0 := eq1197 (M.op x y)
       grind)
    | (have r₁ := eq1197 (M.op x y)
       have r₂ := eq1991
       grind)
    | exact resolve eq1197 eq1991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197 eq1991
  have eq2113 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq2112
  have eq2131 : (M.op (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2113 eq192
    | exact resolve eq192 eq2113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2135 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1865 eq2131
    | exact resolve eq2131 eq1865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131
  have eq2149 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2113 eq2135
    | exact resolve eq2135 eq2113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113 eq2135
  have eq2171 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq179 X0 x
       have i₂ := eq2149
       grind)
    | exact superpose eq2149 eq179
    | exact resolve eq179 eq2149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2177 : (k y x) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq1782 x
       have i₂ := eq2149
       grind)
    | exact superpose eq2149 eq1782
    | exact resolve eq1782 eq2149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq2198 : ∀ X0 : G, (k y x) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2177 eq2171
    | exact resolve eq2171 eq2177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171
  have eq2412 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2198 x
       grind)
    | exact superpose eq2198 eq18
    | (have j1 := eq2198 x
       grind)
    | exact resolve eq18 eq2198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2198
  have eq2643 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq2412
       grind)
    | exact superpose eq2412 eq39
    | exact resolve eq39 eq2412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2645 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq2643
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2643
    | exact resolve eq2643 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2643
  have eq2647 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq2645
    | exact resolve eq2645 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2645
  have eq2650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2647 eq1151
    | exact resolve eq1151 eq2647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647
  have eq2655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq2650
  have eq2662 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq2655
       have r₂ := eq27
       grind)
    | exact resolve eq2655 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2655
  have eq2667 : (k (τ (σ y)) x) = (τ (M.op (M.op x y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2662 eq357
    | exact resolve eq357 eq2662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662
  have eq2702 : (k y x) = (τ (M.op (M.op x y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31 eq2667
    | exact resolve eq2667 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2667
  have eq2716 : (k y x) = (τ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2177 eq2702
    | exact resolve eq2702 eq2177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177 eq2702
  have eq2726 : (M.op x y) = (τ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2412 eq2716
    | exact resolve eq2716 eq2412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412 eq2716
  have eq2736 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2726 eq14
    | exact resolve eq14 eq2726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2726
  have eq2737 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq2736
    | exact resolve eq2736 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2736
  have eq2738 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2737
  have eq2744 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2738 eq184
    | exact resolve eq184 eq2738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2745 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2738 eq204
    | exact resolve eq204 eq2738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2748 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2745
    | exact resolve eq2745 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2745
  have eq2749 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq2744
    | (have j0 := eq2744 X0
       grind)
    | exact resolve eq2744 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744
  have eq2751 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2738 eq2748
    | exact resolve eq2748 eq2738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2748
  have eq2752 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2738 eq2749
    | exact resolve eq2749 eq2738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq2763 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2751 eq250
    | exact resolve eq250 eq2751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2818 : (k (τ (σ x)) x) = (τ (M.op (M.op x y) y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2752 eq357
    | exact resolve eq357 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2879 : (k x x) = (τ (M.op (M.op x y) y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2818
    | exact resolve eq2818 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818
  have eq2900 : (τ (σ x)) = (k x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2751 eq2879
    | exact resolve eq2879 eq2751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2879
  have eq2908 : x = (k x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2900
    | exact resolve eq2900 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2900
  have eq3026 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1195 x x
       have i₂ := eq2908
       grind)
    | exact superpose eq2908 eq1195
    | (have j0 := eq1195 x x
       grind)
    | (have r₁ := eq1195 x x
       have r₂ := eq2908
       grind)
    | exact resolve eq1195 eq2908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2908
  have eq3027 : x ≠ x ∨ x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3026
  have eq3028 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3027
  have eq3035 : (k (σ x) (σ x)) = (σ (M.op (M.op x y) y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq249
       have i₂ := eq3028
       grind)
    | exact superpose eq3028 eq249
    | exact resolve eq249 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028
  have eq3069 : (k (σ x) (σ x)) = (σ (M.op (M.op x y) y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3035
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3035
    | exact resolve eq3035 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035
  have eq3080 : (k (σ x) (σ x)) = (σ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2751 eq3069
    | exact resolve eq3069 eq2751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2751 eq3069
  have eq3084 : (σ x) = (σ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2763 eq3080
    | exact resolve eq3080 eq2763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763 eq3080
  have eq3087 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3084 eq15
    | exact resolve eq15 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3084
  have eq3104 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3087
    | exact resolve eq3087 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3087
  have eq7663 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1843 eq26
    | (have j1 := eq1843 (σ x)
       grind)
    | exact resolve eq26 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq7698 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1865 eq7663
    | exact resolve eq7663 eq1865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865 eq7663
  have eq7726 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7698
       have r₂ := eq27
       grind)
    | exact resolve eq7698 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7698
  have eq7898 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq179 X0 x
       have i₂ := eq7726
       grind)
    | exact superpose eq7726 eq179
    | exact resolve eq179 eq7726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq7904 : (k y x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1782 x
       have i₂ := eq7726
       grind)
    | exact superpose eq7726 eq1782
    | exact resolve eq1782 eq7726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7726
  have eq7951 : ∀ X0 : G, (k y x) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7904 eq7898
    | exact resolve eq7898 eq7904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7898 eq7904
  have eq8094 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7951 x
       grind)
    | exact superpose eq7951 eq18
    | (have j1 := eq7951 x
       grind)
    | exact resolve eq18 eq7951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7951
  have eq8201 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq8094
       grind)
    | exact superpose eq8094 eq39
    | exact resolve eq39 eq8094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq8094
  have eq8207 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8201
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8201
    | exact resolve eq8201 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8201
  have eq8209 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8207
    | exact resolve eq8207 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8207
  have eq8211 : (M.op x y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2738 eq8209
    | exact resolve eq8209 eq2738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2738 eq8209
  have eq8224 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8211 eq1151
    | exact resolve eq1151 eq8211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq8246 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8224
  have eq8369 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8246 eq180
    | exact resolve eq180 eq8246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq8374 : (k (σ y) (σ x)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8246 eq1782
    | exact resolve eq1782 eq8246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782 eq8246
  have eq8414 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8211 eq8374
    | exact resolve eq8374 eq8211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8211 eq8374
  have eq8419 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq204 eq8369
    | exact resolve eq8369 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8369
  have eq8433 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8414 eq8419
    | exact resolve eq8419 eq8414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8414 eq8419
  have eq9245 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8433 eq26
    | (have j1 := eq8433 (σ x)
       grind)
    | exact resolve eq26 eq8433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8433
  have eq9254 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9245
  have eq9275 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9254 eq184
    | exact resolve eq184 eq9254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq9276 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9254 eq204
    | exact resolve eq204 eq9254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq9279 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq9282 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9276
    | exact resolve eq9276 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9276
  have eq9283 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq9275
    | (have j0 := eq9275 X0
       grind)
    | exact resolve eq9275 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9275
  have eq9285 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9254 eq9282
    | exact resolve eq9282 eq9254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9282
  have eq9286 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9254 eq9283
    | exact resolve eq9283 eq9254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9254 eq9283
  have eq9423 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9285 eq250
    | exact resolve eq250 eq9285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq9512 : (k (τ (σ x)) x) = (τ (M.op (M.op x y) y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9286 eq357
    | exact resolve eq357 eq9286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq9620 : (k x x) = (τ (M.op (M.op x y) y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq9512
    | exact resolve eq9512 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9512
  have eq9650 : (τ (σ x)) = (k x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9285 eq9620
    | exact resolve eq9620 eq9285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9620
  have eq9662 : x = (k x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq9650
    | exact resolve eq9650 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9650
  have eq9876 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1195 x x
       have i₂ := eq9662
       grind)
    | exact superpose eq9662 eq1195
    | (have j0 := eq1195 x x
       grind)
    | (have r₁ := eq1195 x x
       have r₂ := eq9662
       grind)
    | exact resolve eq1195 eq9662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9662
  have eq9877 : x ≠ x ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9876
  have eq9878 : x = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9877
  have eq9896 : (k (σ x) (σ x)) = (σ (M.op (M.op x y) y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq249
       have i₂ := eq9878
       grind)
    | exact superpose eq9878 eq249
    | exact resolve eq249 eq9878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq9878
  have eq9965 : (k (σ x) (σ x)) = (σ (M.op (M.op x y) y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9896
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9896
    | exact resolve eq9896 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9896
  have eq9983 : (k (σ x) (σ x)) = (σ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9285 eq9965
    | exact resolve eq9965 eq9285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9285 eq9965
  have eq9994 : (σ x) = (σ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9423 eq9983
    | exact resolve eq9983 eq9423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9423 eq9983
  have eq10012 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9994 eq15
    | exact resolve eq15 eq9994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9994
  have eq10059 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq10012
    | exact resolve eq10012 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10012
  have eq10068 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10059 eq27
    | exact resolve eq27 eq10059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10059
  have eq10077 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10068
       have r₂ := eq3104
       grind)
    | exact resolve eq10068 eq3104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3104 eq10068
  have eq10078 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10077
       grind)
    | exact superpose eq10077 eq18
    | exact resolve eq18 eq10077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10103 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq10077
  have eq10170 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10078 eq9286
    | exact resolve eq9286 eq10078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9286
  have eq10171 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10078 eq2752
    | exact resolve eq2752 eq10078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752 eq10078
  have eq10184 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq10171
  have eq10185 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10170
  have eq10190 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10184
       have r₂ := eq10103
       grind)
    | exact resolve eq10184 eq10103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10103 eq10184
  have eq10191 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10185
       have r₂ := eq9279
       grind)
    | exact resolve eq10185 eq9279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9279 eq10185
  have eq10233 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10191 eq27
    | exact resolve eq27 eq10191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10191
  have eq10242 : x = (M.op x y) := by
    first
    | (have r₁ := eq10233
       have r₂ := eq10190
       grind)
    | exact resolve eq10233 eq10190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10190 eq10233
  have eq10244 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10242
       grind)
    | exact superpose eq10242 eq18
    | exact resolve eq18 eq10242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq10245 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq10242
       grind)
    | exact superpose eq10242 eq22
    | exact resolve eq22 eq10242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10242
  have eq10253 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq10245 eq20
    | exact resolve eq20 eq10245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10245
  have eq10409 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq10244 eq188
    | exact resolve eq188 eq10244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq10412 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq10244 eq221
    | exact resolve eq221 eq10244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq10492 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq10409 eq247
    | exact resolve eq247 eq10409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq10409
  have eq10502 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq10244 eq10492
    | exact resolve eq10492 eq10244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10492
  have eq10521 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq10253 eq10502
    | exact resolve eq10502 eq10253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10502
  have eq10526 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq10521
    | exact resolve eq10521 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10521
  have eq10528 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq10253 eq10526
    | exact resolve eq10526 eq10253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10526
  have eq10706 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10528 eq1195
    | (have j0 := eq1195 (σ x) (σ x)
       grind)
    | (have r₁ := eq1195 (σ x) (σ x)
       have r₂ := eq10528
       grind)
    | exact resolve eq1195 eq10528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq10528
  have eq10707 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq10706
  have eq10708 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq10707
  have eq10751 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10708 eq192
    | exact resolve eq192 eq10708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq10755 : (σ x) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq10708 eq10751
    | exact resolve eq10751 eq10708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10708 eq10751
  have eq10770 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq10244 eq10755
    | exact resolve eq10755 eq10244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10244 eq10755
  have eq10782 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq10770 eq26
    | exact resolve eq26 eq10770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq10904 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10412 eq10782
    | exact resolve eq10782 eq10412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10412 eq10782
  have eq10930 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq10904 eq27
    | exact resolve eq27 eq10904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq10904
  have eq10941 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq10253 eq10930
    | exact resolve eq10930 eq10253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10253 eq10930
  have eq10944 : False := by grind
  exact eq10944
