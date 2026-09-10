import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation1485 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq83 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (M.op x x) = (k y x) := by
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
  have eq84 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq104
    | exact resolve eq104 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq105
    | exact resolve eq105 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq11586 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq11586
    | exact resolve eq11586 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11586
  have eq11598 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq11587
       have r₂ := eq28
       grind)
    | exact resolve eq11587 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11587
  have eq11602 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq11598
    | exact resolve eq11598 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11598
  have eq11607 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11602 eq84
    | (have r₁ := eq84
       have r₂ := eq11602
       grind)
    | exact resolve eq84 eq11602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq11602
  have eq11661 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq11607
  have eq11662 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq11661
  have eq11668 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11662 eq106
    | exact resolve eq106 eq11662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq11662
  have eq11677 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11668
  have eq11680 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11677
       have r₂ := eq28
       grind)
    | exact resolve eq11677 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11677
  have eq11682 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq11680
       grind)
    | exact superpose eq11680 eq52
    | exact resolve eq52 eq11680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq11684 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq11680
       grind)
    | exact superpose eq11680 eq83
    | (have r₁ := eq83
       have r₂ := eq11680
       grind)
    | exact resolve eq83 eq11680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq11680
  have eq11737 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq11684
  have eq11738 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11737
  have eq11750 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq11682
    | exact resolve eq11682 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11682
  have eq12104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq11738
       grind)
    | exact superpose eq11738 eq91
    | exact resolve eq91 eq11738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq11738
  have eq12120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq12104
    | exact resolve eq12104 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12104
  have eq12210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12120 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq12120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12120
  have eq12211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12210
  have eq12215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq12211
    | exact resolve eq12211 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12211
  have eq12226 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12215
       have r₂ := eq28
       grind)
    | exact resolve eq12215 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12215
  have eq12230 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq12226
    | exact resolve eq12226 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12226
  have eq12414 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12230 eq11750
    | exact resolve eq11750 eq12230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11750 eq12230
  have eq12465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12414
  have eq12469 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12465
       have r₂ := eq28
       grind)
    | exact resolve eq12465 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12465
  have eq12472 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq12469 eq30
    | exact resolve eq30 eq12469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12469
  have eq12596 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq12472
    | exact resolve eq12472 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12472
  have eq12597 : x = y := by grind
  clear eq12596
  have eq12616 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq12597
       grind)
    | exact superpose eq12597 eq19
    | exact resolve eq19 eq12597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq12617 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq12597
       grind)
    | exact superpose eq12597 eq25
    | exact resolve eq25 eq12597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12597
  have eq12740 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq12617
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12617
    | exact resolve eq12617 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq12617
  have eq12948 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12740 eq27
    | exact resolve eq27 eq12740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq12740
  have eq13207 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12948 eq71
    | exact resolve eq71 eq12948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq12948
  have eq13286 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13207
       have i₂ := eq12616
       grind)
    | exact superpose eq12616 eq13207
    | exact resolve eq13207 eq12616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12616 eq13207
  have eq13295 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13286 eq15
    | exact resolve eq15 eq13286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13286
  have eq13339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq13295
    | exact resolve eq13295 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq13295
  have eq13348 : False := by grind
  exact eq13348

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq91 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq104
    | exact resolve eq104 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq703 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq712 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq703 X0
       grind)
    | exact superpose eq703 eq14
    | exact resolve eq14 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq1057 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq712
    | exact resolve eq712 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq9361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq105 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq9362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq9361
    | exact resolve eq9361 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9361
  have eq9373 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq9362
       have r₂ := eq28
       grind)
    | exact resolve eq9362 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9362
  have eq9378 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9373 eq14
    | exact resolve eq14 eq9373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9393 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq9373 eq1057
    | exact resolve eq1057 eq9373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9403 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9378 x
       have i₂ := eq1057 sF3 x
       grind)
    | exact superpose eq1057 eq9378
    | exact resolve eq9378 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9378
  have eq16982 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq9393 eq9403
    | exact resolve eq9403 eq9393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9393 eq9403
  have eq17037 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq16982
  have eq18036 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq17037 eq9373
    | exact resolve eq9373 eq17037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9373 eq17037
  have eq18073 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18036
  have eq18078 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18073
       grind)
    | exact superpose eq18073 eq14
    | exact resolve eq14 eq18073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18127 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18078 X0
       have i₂ := eq1057 y X0
       grind)
    | exact superpose eq1057 eq18078
    | exact resolve eq18078 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057 eq18078
  have eq18879 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18127 x
       have i₂ := eq18073
       grind)
    | exact superpose eq18073 eq18127
    | exact resolve eq18127 eq18073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18127
  have eq18936 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18879
  have eq18951 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18073
       have i₂ := eq18936
       grind)
    | exact superpose eq18936 eq18073
    | exact resolve eq18073 eq18936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18073 eq18936
  have eq18990 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq18951
  have eq19974 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq18990 eq30
    | exact resolve eq30 eq18990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18990
  have eq20099 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq19974
    | exact resolve eq19974 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19974
  have eq20100 : x = y := by grind
  clear eq20099
  have eq20119 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq20100
       grind)
    | exact superpose eq20100 eq19
    | exact resolve eq19 eq20100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20120 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20100
       grind)
    | exact superpose eq20100 eq25
    | exact resolve eq25 eq20100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20100
  have eq20242 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20120
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20120
    | exact resolve eq20120 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq20120
  have eq20257 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20242 eq27
    | exact resolve eq27 eq20242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20242
  have eq21376 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20257 eq70
    | exact resolve eq70 eq20257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq20257
  have eq21460 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq21376
       have i₂ := eq20119
       grind)
    | exact superpose eq20119 eq21376
    | exact resolve eq21376 eq20119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20119 eq21376
  have eq22553 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21460 eq15
    | exact resolve eq15 eq21460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21460
  have eq22601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq22553
    | exact resolve eq22553 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22553
  have eq22610 : False := by grind
  exact eq22610

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq108 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq187 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq207 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq108 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq211 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq207 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq207
    | exact resolve eq207 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq207 X0
       grind)
    | exact superpose eq207 eq9
    | exact resolve eq9 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq247 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq211 X0
       grind)
    | exact superpose eq211 eq9
    | exact resolve eq9 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq279 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq217
    | exact resolve eq217 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq304 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq279 X0 X1
       grind)
    | exact superpose eq279 eq9
    | exact resolve eq9 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1958 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq187 x y
       grind)
    | exact superpose eq187 eq16
    | (have j1 := eq187 x y
       grind)
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq20966 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq186 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq186
    | exact resolve eq186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq21087 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20966 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq20966
    | (have j0 := eq20966 X0 X1
       grind)
    | exact resolve eq20966 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20966
  have eq32340 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1958
       have i₂ := eq21087 x y
       grind)
    | exact superpose eq21087 eq1958
    | (have j1 := eq21087 (σ x) (σ y)
       grind)
    | (have r₁ := eq1958
       have r₂ := eq21087 x y
       grind)
    | (have r₁ := eq1958
       have r₂ := eq21087 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1958
       have r₂ := eq21087 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1958 eq21087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958 eq21087
  have eq32341 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq32340
  have eq78133 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32341
       grind)
    | exact superpose eq32341 eq16
    | exact resolve eq16 eq32341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32341
  have eq78134 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq78133
       have r₂ := eq22 x
       grind)
    | exact resolve eq78133 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78133
  have eq78157 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq279 y x
       have i₂ := eq78134
       grind)
    | exact superpose eq78134 eq279
    | exact resolve eq279 eq78134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78134
  have eq78259 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq279 (σ y) (σ x)
       have i₂ := eq78157
       grind)
    | exact superpose eq78157 eq279
    | exact resolve eq279 eq78157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78157
  have eq78315 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78259
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq78259
    | exact resolve eq78259 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78259
  have eq78357 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq78315
       grind)
    | exact superpose eq78315 eq10
    | exact resolve eq10 eq78315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78315
  have eq78468 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78357
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq78357
    | exact resolve eq78357 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78357
  have eq78470 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78468
       grind)
    | exact superpose eq78468 eq16
    | exact resolve eq16 eq78468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78468
  have eq78471 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq78470
       have r₂ := eq22 x
       grind)
    | exact resolve eq78470 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq78470
  have eq78517 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq78471
       grind)
    | exact superpose eq78471 eq10
    | exact resolve eq10 eq78471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78471
  have eq78629 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78517
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq78517
    | exact resolve eq78517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78517
  have eq78630 : y = (M.op y y) := by grind
  clear eq78629
  have eq78687 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq247 y X0
       have i₂ := eq78630
       grind)
    | exact superpose eq78630 eq247
    | exact resolve eq247 eq78630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq78822 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq78630
       grind)
    | exact superpose eq78630 eq9
    | exact resolve eq9 eq78630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78843 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq304 y y x
       have i₂ := eq78630
       grind)
    | exact superpose eq78630 eq304
    | exact resolve eq304 eq78630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78630
  have eq78887 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq78843 X0
       have i₂ := eq279 y X0
       grind)
    | exact superpose eq279 eq78843
    | exact resolve eq78843 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq78843
  have eq79119 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq78822 X0
       have i₂ := eq78887 X0
       grind)
    | exact superpose eq78887 eq78822
    | exact resolve eq78822 eq78887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79196 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) y) X1) = (M.op (M.op (M.op (M.op (M.op y X0) y) X1) X0) (M.op (M.op (M.op y X0) y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq304 (M.op (M.op y X0) y) X1 X0
       have i₂ := eq78822 X0
       grind)
    | exact superpose eq78822 eq304
    | exact resolve eq304 eq78822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq78822
  have eq79252 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79196 X0 X1
       have i₂ := eq78887 X0
       grind)
    | exact superpose eq78887 eq79196
    | exact resolve eq79196 eq78887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79196
  have eq79293 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79252 X0 X0
       have i₂ := eq79119 X0
       grind)
    | exact superpose eq79119 eq79252
    | exact resolve eq79252 eq79119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79252
  have eq79318 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq78887 X0
       have i₂ := eq79119 X0
       grind)
    | exact superpose eq79119 eq78887
    | exact resolve eq78887 eq79119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78887 eq79119
  have eq81566 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq79293 X0 (M.op (M.op (σ y) X0) (σ y))
       have i₂ := eq78687 X0
       grind)
    | exact superpose eq78687 eq79293
    | exact resolve eq79293 eq78687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78687
  have eq81573 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq81566 X0
       have i₂ := eq79293 X0 (σ y)
       grind)
    | exact superpose eq79293 eq81566
    | exact resolve eq81566 eq79293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79293 eq81566
  have eq83001 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81573 (σ x)
       grind)
    | exact superpose eq81573 eq16
    | exact resolve eq16 eq81573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81573
  have eq83106 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq83001
       have i₂ := eq79318 x
       grind)
    | exact superpose eq79318 eq83001
    | exact resolve eq83001 eq79318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79318 eq83001
  have eq83107 : False := by grind
  exact eq83107

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq109 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq196 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
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
  have eq199 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq194
    | (have j0 := eq194 X0 X1
       grind)
    | exact resolve eq194 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq220 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq109 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq109
    | exact resolve eq109 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq228 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq9
    | exact resolve eq9 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq287 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq228 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq228
    | exact resolve eq228 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq228 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq110 X0 (σ X0)
       grind)
    | exact superpose eq110 eq228
    | exact resolve eq228 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq228
  have eq1978 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq199 x y
       grind)
    | exact superpose eq199 eq16
    | (have j1 := eq199 x y
       grind)
    | exact resolve eq16 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq14454 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq196 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq196
    | exact resolve eq196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq14739 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14454 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14454
    | (have j0 := eq14454 X0 X1
       grind)
    | exact resolve eq14454 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14454
  have eq19984 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq1978
       have i₂ := eq14739 y x
       grind)
    | exact superpose eq14739 eq1978
    | (have j1 := eq14739 y x
       grind)
    | (have r₁ := eq1978
       have r₂ := eq14739 y x
       grind)
    | (have r₁ := eq1978
       have r₂ := eq14739 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1978
       have r₂ := eq14739 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1978 eq14739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1978 eq14739
  have eq19985 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq19984
  have eq22690 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19985
       grind)
    | exact superpose eq19985 eq16
    | exact resolve eq16 eq19985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19985
  have eq22691 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq22690
       have r₂ := eq23 x
       grind)
    | exact resolve eq22690 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22690
  have eq22693 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22691
       grind)
    | exact superpose eq22691 eq10
    | exact resolve eq10 eq22691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22691
  have eq22780 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq22693
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22693
    | exact resolve eq22693 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22693
  have eq22782 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22780
       grind)
    | exact superpose eq22780 eq16
    | exact resolve eq16 eq22780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22780
  have eq22783 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq22782
       have r₂ := eq23 x
       grind)
    | exact resolve eq22782 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22782
  have eq22819 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq22783
       grind)
    | exact superpose eq22783 eq10
    | exact resolve eq10 eq22783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22783
  have eq22906 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22819
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq22819
    | exact resolve eq22819 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22819
  have eq22907 : y = (M.op x x) := by grind
  clear eq22906
  have eq22953 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq289 x
       have i₂ := eq22907
       grind)
    | exact superpose eq22907 eq289
    | exact resolve eq289 eq22907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq23062 : y = (M.op x y) := by
    first
    | (have i₁ := eq287 x x
       have i₂ := eq22907
       grind)
    | exact superpose eq22907 eq287
    | exact resolve eq287 eq22907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq22907
  have eq23572 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22953
       grind)
    | exact superpose eq22953 eq16
    | exact resolve eq16 eq22953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22953
  have eq23657 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq23572
       have i₂ := eq23062
       grind)
    | exact superpose eq23062 eq23572
    | exact resolve eq23572 eq23062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23062 eq23572
  have eq23658 : False := by grind
  exact eq23658

/-- `Equation4416`: `x ◇ (x ◇ y) = (z ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_y_pxy_x_pxy_Equation4416 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4416 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4416.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
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
  have eq29 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 X0 (M.op x y)
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
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq28
    | (have j0 := eq28 (M.op x y)
       grind)
    | exact resolve eq28 eq20
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
  have eq35 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 X0 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq41 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29
    | (have j0 := eq29 x
       grind)
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
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
  have eq52 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 y X0 x
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op x X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2
       have i₂ := eq9 (M.op X0 X1) X2 X0
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq55 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X1 (M.op X1 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 X1 X2
       have i₂ := eq9 X1 (M.op (M.op X0 X1) X2) X0
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq56 : ∀ X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X1 (M.op X1 (M.op X1 (M.op X1 X2)))) := by
    intro X1 X2
    first
    | (have i₁ := eq55 x X1 X2
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq59 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq30 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30
    | (have j0 := eq30 x
       grind)
    | exact resolve eq30 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq30
  have eq65 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq215 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X0 (M.op X1 X0))) ∨ (M.op (M.op X1 X0) X2) = (k (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X0) X2
       have i₂ := eq9 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 X0) X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 : G, (M.op x y) ≠ (M.op y (M.op y (M.op x y))) ∨ (k (M.op x y) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq52 eq12
    | (have j0 := eq12 (M.op x y) X0
       grind)
    | exact resolve eq12 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op x y) ≠ (M.op y (M.op y (M.op x y))) ∨ (k (M.op x y) X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq52 eq216
    | exact resolve eq216 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq220 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X0 (M.op X1 X0))) ∨ (k (M.op X1 X0) X2) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq215 X0 X1 X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq215
    | (have j0 := eq215 X0 X1 X2
       grind)
    | exact resolve eq215 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1091 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq1123 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq32
       have i₂ := eq14 sF1 sF1
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1129 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq59
       have i₂ := eq14 sF2 sF2
       grind)
    | exact superpose eq14 eq59
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1135 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq14 sF3 sF3
       grind)
    | exact superpose eq14 eq70
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq70 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1135
  have eq1137 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1129
  have eq1138 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1123
  have eq1333 : (σ (k y (k x x))) = (k (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 (k x x)
       have i₂ := eq1137
       grind)
    | exact superpose eq1137 eq36
    | exact resolve eq36 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1137
  have eq5773 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 X0
       have i₂ := eq1091 X0 (τ X1)
       grind)
    | exact superpose eq1091 eq48
    | (have j1 := eq1091 X0 (τ X1)
       grind)
    | exact resolve eq48 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5908 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5773 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5773
    | (have j0 := eq5773 X0 X1
       grind)
    | exact resolve eq5773 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5773
  have eq5967 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5908 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq5908 (τ X1) X1
       have r₂ := eq12 (σ (τ X1)) X1
       grind)
    | (have r₁ := eq5908 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq5908 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5908
  have eq6003 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5967 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5967
    | (have j0 := eq5967 X0 X1
       grind)
    | exact resolve eq5967 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5967
  have eq6060 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6003 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6003
    | exact resolve eq6003 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6003
  have eq6360 : (σ (k x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq41
       have i₂ := eq6060 sF2 sF1
       grind)
    | exact superpose eq6060 eq41
    | (have j1 := eq6060 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq6060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq6372 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq65
       have i₂ := eq6060 sF2 sF3
       grind)
    | exact superpose eq6060 eq65
    | (have j1 := eq6060 (σ x) (σ y)
       grind)
    | exact resolve eq65 eq6060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq6374 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq6372
    | exact resolve eq6372 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6372
  have eq6384 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6374
       have i₂ := eq6060 x y
       grind)
    | exact superpose eq6060 eq6374
    | (have j1 := eq6060 (σ x) (σ y)
       grind)
    | exact resolve eq6374 eq6060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6374
  have eq6405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6384
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6384
    | exact resolve eq6384 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6384
  have eq6409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq6405
    | exact resolve eq6405 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6405
  have eq6411 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq6409
       have r₂ := eq27
       grind)
    | exact resolve eq6409 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6409
  have eq6417 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op (σ x) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq6411 eq9
    | exact resolve eq9 eq6411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6424 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6417 eq6411
    | exact resolve eq6411 eq6417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6417
  have eq6438 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ y = (M.op y x) := by grind
  clear eq6424
  have eq6447 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6438 eq56
    | exact resolve eq56 eq6438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6449 : ∀ X0 : G, (σ y) ≠ (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ x)) (σ y))) ∨ (k (σ y) X0) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ x)) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq6438 eq220
    | exact resolve eq220 eq6438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6438
  have eq6458 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ y)))) ∨ (k (σ y) X0) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ x)) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq6449 X0
       have i₂ := eq9 sF2 (M.op (M.op sF2 sF2) sF3) sF2
       grind)
    | exact superpose eq9 eq6449
    | (have j0 := eq6449 X0
       grind)
    | exact resolve eq6449 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6449
  have eq6460 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq6447
    | exact resolve eq6447 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6447
  have eq6463 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (k (σ y) X0) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ x)) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq6458 X0
       have i₂ := eq9 sF2 sF3 sF2
       grind)
    | exact superpose eq9 eq6458
    | (have j0 := eq6458 X0
       grind)
    | exact resolve eq6458 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6458
  have eq6465 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k (σ y) X0) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ x)) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq6463 X0
       have i₂ := eq56 sF2 (M.op sF2 (M.op sF2 sF3))
       grind)
    | (have i₁ := eq6463 X0
       have i₂ := eq56 sF2 sF3
       grind)
    | exact superpose eq56 eq6463
    | (have j0 := eq6463 X0
       grind)
    | exact resolve eq6463 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6463
  have eq6466 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k (σ y) X0) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ x)) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq6465
    | (have j0 := eq6465 X0
       grind)
    | exact resolve eq6465 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6465
  have eq6467 : ∀ X0 : G, (k (σ y) X0) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ x)) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq6466 X0
       grind)
    | (have r₁ := eq6466 X0
       have r₂ := eq6460
       grind)
    | exact resolve eq6466 eq6460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6466
  have eq6468 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq6467 X0
       have i₂ := eq9 sF2 (M.op (M.op sF2 sF2) X0) sF2
       grind)
    | exact superpose eq9 eq6467
    | exact resolve eq6467 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6467
  have eq6469 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) X0)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq6468 x
       have i₂ := eq9 sF2 x sF2
       grind)
    | exact superpose eq9 eq6468
    | exact resolve eq6468 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6468
  have eq6470 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ x) (M.op (σ x) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq6469 X0
       have i₂ := eq56 sF2 (M.op sF2 (M.op sF2 X0))
       grind)
    | (have i₁ := eq6469 x
       have i₂ := eq56 sF2 x
       grind)
    | exact superpose eq56 eq6469
    | exact resolve eq6469 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6469
  have eq6592 : (σ (k y y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6470 eq70
    | exact resolve eq70 eq6470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq6470
  have eq6595 : (σ (k y y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq6592
    | exact resolve eq6592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6592
  have eq6612 : (k y y) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq6595
       grind)
    | exact superpose eq6595 eq10
    | exact resolve eq10 eq6595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6595
  have eq6633 : (τ (σ y)) = (k y y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6460 eq6612
    | exact resolve eq6612 eq6460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6460 eq6612
  have eq6663 : (τ (σ y)) = (k y y) ∨ y = (M.op y x) := by grind
  clear eq6633
  have eq6666 : y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq39 eq6663
    | exact resolve eq6663 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6663
  have eq6672 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1091 y y
       have i₂ := eq6666
       grind)
    | exact superpose eq6666 eq1091
    | (have j0 := eq1091 y y
       grind)
    | exact resolve eq1091 eq6666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq6674 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq6666
       grind)
    | exact superpose eq6666 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq6666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6666
  have eq6676 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq6674
  have eq6677 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq6672
  have eq6682 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6677
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6677
    | exact resolve eq6677 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6677
  have eq6689 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq6676
       grind)
    | exact superpose eq6676 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6676
       grind)
    | exact resolve eq12 eq6676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6676
  have eq6690 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq6689 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6689
  have eq6696 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k (σ y) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq6682 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ y) x
       have r₂ := eq6682
       grind)
    | exact resolve eq12 eq6682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6682
  have eq6697 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq6696 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6696
  have eq6847 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6697 eq60
    | exact resolve eq60 eq6697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6697
  have eq6939 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq6847
       grind)
    | exact superpose eq6847 eq10
    | exact resolve eq10 eq6847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6847
  have eq7089 : (τ (σ y)) = (k y x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6411 eq6939
    | exact resolve eq6939 eq6411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6411 eq6939
  have eq7121 : (τ (σ y)) = (k y x) ∨ y = (M.op y x) := by grind
  clear eq7089
  have eq7124 : y = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq39 eq7121
    | exact resolve eq7121 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7121
  have eq7129 : y = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6690 x
       have i₂ := eq7124
       grind)
    | exact superpose eq7124 eq6690
    | exact resolve eq6690 eq7124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6690 eq7124
  have eq7137 : y = (M.op y x) := by grind
  clear eq7129
  have eq7144 : ∀ X0 : G, y ≠ (M.op x (M.op x y)) ∨ (k y X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq220 x y x
       have i₂ := eq7137
       grind)
    | exact superpose eq7137 eq220
    | exact resolve eq220 eq7137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7149 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq7137
       grind)
    | exact superpose eq7137 eq9
    | exact resolve eq9 eq7137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7151 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y (M.op x (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq7149 X0
       grind)
    | exact superpose eq7149 eq52
    | exact resolve eq52 eq7149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq7152 : ∀ X0 : G, (k (M.op x y) X0) = (M.op y (M.op x (M.op x X0))) ∨ (M.op x y) ≠ (M.op y (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq219 X0
       have i₂ := eq7149 X0
       grind)
    | exact superpose eq7149 eq219
    | exact resolve eq219 eq7149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq7191 : y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq7137
       have i₂ := eq7149 x
       grind)
    | exact superpose eq7149 eq7137
    | exact resolve eq7137 eq7149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7137
  have eq7197 : ∀ X0 : G, y ≠ (M.op x (M.op x y)) ∨ (k y X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq7144 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7144
    | (have j0 := eq7144 X0
       grind)
    | exact resolve eq7144 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7144
  have eq7223 : ∀ X0 : G, (k (M.op x y) X0) = (M.op x (M.op x (M.op x (M.op x X0)))) ∨ (M.op x y) ≠ (M.op y (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq7152 X0
       have i₂ := eq7149 (M.op x (M.op x X0))
       grind)
    | exact superpose eq7149 eq7152
    | exact resolve eq7152 eq7149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7152
  have eq7224 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x (M.op x (M.op x (M.op x X0)))) := by
    intro X0
    first
    | (have i₁ := eq7151 X0
       have i₂ := eq7149 (M.op x (M.op x X0))
       grind)
    | exact superpose eq7149 eq7151
    | exact resolve eq7151 eq7149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7151
  have eq7250 : ∀ X0 : G, (k (M.op x y) X0) = (M.op x (M.op x X0)) ∨ (M.op x y) ≠ (M.op y (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq7223 X0
       have i₂ := eq56 x X0
       grind)
    | (have i₁ := eq7223 X0
       have i₂ := eq56 x (M.op x (M.op x X0))
       grind)
    | exact superpose eq56 eq7223
    | exact resolve eq7223 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7223
  have eq7251 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq7224 X0
       have i₂ := eq56 x X0
       grind)
    | (have i₁ := eq7224 X0
       have i₂ := eq56 x (M.op x (M.op x X0))
       grind)
    | exact superpose eq56 eq7224
    | exact resolve eq7224 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7224
  have eq7260 : ∀ X0 : G, (M.op x y) ≠ (M.op x (M.op x (M.op y (M.op x y)))) ∨ (k (M.op x y) X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq7250 X0
       have i₂ := eq7149 (M.op y sF0)
       grind)
    | exact superpose eq7149 eq7250
    | (have j0 := eq7250 X0
       grind)
    | exact resolve eq7250 eq7149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7250
  have eq7266 : ∀ X0 : G, (M.op x y) ≠ (M.op x (M.op x (M.op x (M.op x (M.op x y))))) ∨ (k (M.op x y) X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq7260 X0
       have i₂ := eq7149 sF0
       grind)
    | exact superpose eq7149 eq7260
    | (have j0 := eq7260 X0
       grind)
    | exact resolve eq7260 eq7149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7149 eq7260
  have eq7271 : ∀ X0 : G, (M.op x y) ≠ (M.op x (M.op x (M.op x y))) ∨ (k (M.op x y) X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq7266 X0
       have i₂ := eq56 x (M.op x (M.op x sF0))
       grind)
    | (have i₁ := eq7266 X0
       have i₂ := eq56 x sF0
       grind)
    | exact superpose eq56 eq7266
    | (have j0 := eq7266 X0
       grind)
    | exact resolve eq7266 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7266
  have eq7321 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq7191
       grind)
    | exact superpose eq7191 eq56
    | exact resolve eq56 eq7191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7325 : (M.op x y) = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq56 x (M.op x x)
       have i₂ := eq7191
       grind)
    | exact superpose eq7191 eq56
    | exact resolve eq56 eq7191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq7330 : (M.op x y) = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq7325
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7325
    | exact resolve eq7325 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7325
  have eq7334 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq7321
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7321
    | exact resolve eq7321 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7321
  have eq7337 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq7330 eq7271
    | (have j0 := eq7271 X0
       grind)
    | (have r₁ := eq7271 X0
       have r₂ := eq7330
       grind)
    | exact resolve eq7271 eq7330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7271 eq7330
  have eq7339 : ∀ X0 : G, (k (M.op x y) X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq7337 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7337
  have eq7342 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq7334 eq7197
    | (have j0 := eq7197 X0
       grind)
    | (have r₁ := eq7197 X0
       have r₂ := eq7334
       grind)
    | exact resolve eq7197 eq7334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7197
  have eq7346 : ∀ X0 : G, (k y X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq7342 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7342
  have eq7354 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (M.op x (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq7339 eq28
    | exact resolve eq28 eq7339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq7574 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x x))) := by
    first
    | exact superpose eq7339 eq33
    | exact resolve eq33 eq7339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq7580 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op x (M.op x (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7339 eq1138
    | exact resolve eq1138 eq7339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138 eq7339
  have eq7815 : (k (σ y) (M.op (σ x) (σ x))) = (σ (M.op x (M.op x (k x x)))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1333
       have i₂ := eq7346 (k x x)
       grind)
    | exact superpose eq7346 eq1333
    | exact resolve eq1333 eq7346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq7819 : (k (σ y) (σ x)) = (σ (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq60
       have i₂ := eq7346 x
       grind)
    | exact superpose eq7346 eq60
    | exact resolve eq60 eq7346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq7825 : (M.op (σ y) (σ y)) = (σ (M.op x (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1136
       have i₂ := eq7346 y
       grind)
    | exact superpose eq7346 eq1136
    | exact resolve eq1136 eq7346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq7890 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7334 eq7580
    | exact resolve eq7580 eq7334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7580
  have eq7896 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq7574
       have i₂ := eq7191
       grind)
    | exact superpose eq7191 eq7574
    | exact resolve eq7574 eq7191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7574
  have eq7971 : (M.op (σ y) (σ y)) = (σ (M.op x (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7825
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7825
    | exact resolve eq7825 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7825
  have eq7977 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq7819
       have i₂ := eq7191
       grind)
    | exact superpose eq7191 eq7819
    | exact resolve eq7819 eq7191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7819
  have eq8031 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq7890
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7890
    | exact resolve eq7890 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7890
  have eq8037 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq7896
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7896
    | exact resolve eq7896 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7896
  have eq8086 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq7334 eq7971
    | exact resolve eq7971 eq7334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7971
  have eq8091 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq7977
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7977
    | exact resolve eq7977 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7977
  have eq8115 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq8031
    | exact resolve eq8031 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8031
  have eq8116 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq8115
  have eq8149 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq8086
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8086
    | exact resolve eq8086 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8086
  have eq8150 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq8149
  have eq8320 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq8116 eq12
    | (have j0 := eq12 (σ (M.op x y)) X0
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) x
       have r₂ := eq8116
       grind)
    | exact resolve eq12 eq8116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8321 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq8320 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8320
  have eq8406 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ X0)) = (σ (M.op x (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq8321 eq7354
    | exact resolve eq7354 eq8321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7354
  have eq8500 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq8321 eq8037
    | exact resolve eq8037 eq8321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8037 eq8321
  have eq8506 : (σ (k x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8500 eq6360
    | exact resolve eq6360 eq8500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6360
  have eq8628 : (k (σ y) (M.op (σ x) (σ x))) = (M.op (σ (M.op x y)) (σ (k x x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7815
       have i₂ := eq8406 (k x x)
       grind)
    | exact superpose eq8406 eq7815
    | exact resolve eq7815 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7815
  have eq8662 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k (σ y) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq8500 eq220
    | exact resolve eq220 eq8500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq8666 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq8500 eq9
    | exact resolve eq9 eq8500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8708 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq8666 eq8150
    | exact resolve eq8150 eq8666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8150 eq8666
  have eq8712 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k (σ y) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq8662
    | (have j0 := eq8662 X0
       grind)
    | exact resolve eq8662 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8662
  have eq8713 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq8708
    | exact resolve eq8708 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8708
  have eq8725 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq8713 eq8712
    | (have j0 := eq8712 X0
       grind)
    | (have r₁ := eq8712 X0
       have r₂ := eq8713
       grind)
    | exact resolve eq8712 eq8713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8712
  have eq8726 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have j0 := eq8725 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8725
  have eq8820 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ x)))) = (M.op (σ (M.op x y)) (σ (k x x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8726 eq8628
    | exact resolve eq8628 eq8726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8628
  have eq8907 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq8726 eq8091
    | exact resolve eq8091 eq8726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8091
  have eq8927 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (k x x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8907 eq8820
    | exact resolve eq8820 eq8907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8820 eq8907
  have eq8943 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (k x x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq8927
    | exact resolve eq8927 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8927
  have eq9131 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq8406 (M.op x x)
       have i₂ := eq7191
       grind)
    | exact superpose eq7191 eq8406
    | exact resolve eq8406 eq7191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9179 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq9131
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9131
    | exact resolve eq9131 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq9131
  have eq9183 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by
    first
    | exact superpose eq20 eq9179
    | exact resolve eq9179 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9179
  have eq10189 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op x (M.op x (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq48 X0 y
       have i₂ := eq7346 (τ X0)
       grind)
    | exact superpose eq7346 eq48
    | exact resolve eq48 eq7346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq7346
  have eq10251 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ (M.op x y)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10189 X0
       have i₂ := eq8406 (τ X0)
       grind)
    | exact superpose eq8406 eq10189
    | exact resolve eq10189 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8406 eq10189
  have eq10285 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq10251 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10251
    | exact resolve eq10251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10251
  have eq10319 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq10285 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10285
    | (have j0 := eq10285 X0
       grind)
    | exact resolve eq10285 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10285
  have eq10347 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq8726 eq10319
    | exact resolve eq10319 eq8726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8726 eq10319
  have eq11143 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq8713 eq10347
    | exact resolve eq10347 eq8713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11144 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq10347 eq10347
    | exact resolve eq10347 eq10347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11170 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq11143
    | exact resolve eq11143 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11143
  have eq11565 : (M.op (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq8506
       have i₂ := eq6060 x sF0
       grind)
    | exact superpose eq6060 eq8506
    | (have j1 := eq6060 x (M.op x y)
       grind)
    | exact resolve eq8506 eq6060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6060 eq8506
  have eq11584 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq7334 eq11565
    | exact resolve eq11565 eq7334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7334 eq11565
  have eq11586 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq11584
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11584
    | exact resolve eq11584 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11584
  have eq11588 : (M.op x y) = (M.op x (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7251 eq11586
    | exact resolve eq11586 eq7251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7251 eq11586
  have eq11590 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11588
       have i₂ := eq7191
       grind)
    | exact superpose eq7191 eq11588
    | exact resolve eq11588 eq7191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11588
  have eq12138 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11590 eq10347
    | exact resolve eq10347 eq11590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10347 eq11590
  have eq12150 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8116 eq12138
    | exact resolve eq12138 eq8116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8116 eq12138
  have eq12154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq12150
    | exact resolve eq12150 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12150
  have eq12156 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12154
       have r₂ := eq27
       grind)
    | exact resolve eq12154 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12154
  have eq12159 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12156 eq39
    | exact resolve eq39 eq12156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq12156
  have eq12167 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq12159
    | exact resolve eq12159 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq12159
  have eq12168 : y = (M.op x y) := by grind
  clear eq12167
  have eq12171 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq12168 eq20
    | exact resolve eq20 eq12168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq12168
  have eq12649 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12171
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12171
    | exact resolve eq12171 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12171
  have eq12650 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq12649 eq24
    | exact resolve eq24 eq12649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq12651 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq12649 eq26
    | exact resolve eq26 eq12649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq12815 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq12649 eq8500
    | exact resolve eq8500 eq12649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8500
  have eq12822 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12649 eq8713
    | exact resolve eq8713 eq12649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8713 eq12649
  have eq13285 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq12815 eq11144
    | exact resolve eq11144 eq12815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11144
  have eq13304 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq12651 eq13285
    | exact resolve eq13285 eq12651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12651 eq13285
  have eq14839 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8943
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq8943
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq8943 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8943
  have eq14854 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq14839
  have eq14863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq9183 eq14854
    | exact resolve eq14854 eq9183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9183 eq14854
  have eq14866 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq14863
       have r₂ := eq27
       grind)
    | exact resolve eq14863 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14863
  have eq14870 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14866 eq13304
    | exact resolve eq13304 eq14866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13304 eq14866
  have eq14881 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq12815 eq14870
    | exact resolve eq14870 eq12815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12815 eq14870
  have eq14886 : x = (M.op x x) := by
    first
    | (have r₁ := eq14881
       have r₂ := eq27
       grind)
    | exact resolve eq14881 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14881
  have eq14889 : y = (M.op x x) := by
    first
    | (have i₁ := eq7191
       have i₂ := eq14886
       grind)
    | exact superpose eq14886 eq7191
    | exact resolve eq7191 eq14886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7191
  have eq14920 : x = y := by
    first
    | (have i₁ := eq14889
       have i₂ := eq14886
       grind)
    | exact superpose eq14886 eq14889
    | exact resolve eq14889 eq14886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14886 eq14889
  have eq15108 : (σ x) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq12650
       have i₂ := eq14920
       grind)
    | exact superpose eq14920 eq12650
    | exact resolve eq12650 eq14920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12650 eq14920
  have eq15812 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15108
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15108
    | exact resolve eq15108 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15108
  have eq16437 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15812 eq12822
    | exact resolve eq12822 eq15812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12822 eq15812
  have eq16807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11170 eq16437
    | exact resolve eq16437 eq11170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11170 eq16437
  have eq17103 : False := by grind
  exact eq17103

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pxy_pyx_Equation840 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law840 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ x) (σ y)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq79 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X1)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq12
    | (have j0 := eq12 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq12 X1 (M.op X0 X1)
       have r₂ := eq56 X0 X1
       grind)
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : y ≠ y ∨ y = (M.op x y) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq57 eq12
    | (have j0 := eq12 y (M.op x y)
       grind)
    | (have r₁ := eq12 y (M.op x y)
       have r₂ := eq57
       grind)
    | exact resolve eq12 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq65 eq12
    | (have j0 := eq12 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq65
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq89 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq88
  have eq92 : y = (k y (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq84
  have eq93 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq103 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq111
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq111
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq111 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq118
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq118
    | exact resolve eq118 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq124
    | exact resolve eq124 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq891 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X1) (σ X0)
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq56
    | (have j1 := eq67 X0 X1
       grind)
    | exact resolve eq56 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq15121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq125 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq15121
    | exact resolve eq15121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15121
  have eq15133 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq15122
       have r₂ := eq28
       grind)
    | exact resolve eq15122 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15122
  have eq15137 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq15133 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15133
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15133
       grind)
    | exact resolve eq12 eq15133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15140 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq15133 eq56
    | exact resolve eq56 eq15133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15133
  have eq15158 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq15137
  have eq15159 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq15158
  have eq15160 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq15140
    | exact resolve eq15140 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15140
  have eq15164 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq15160
       grind)
    | exact superpose eq15160 eq56
    | exact resolve eq56 eq15160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15168 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq93 x y
       have i₂ := eq15160
       grind)
    | exact superpose eq15160 eq93
    | exact resolve eq93 eq15160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq15160
  have eq15181 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15168
  have eq15184 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq15191 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15184 eq89
    | exact resolve eq89 eq15184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq15184
  have eq15211 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq15191
  have eq15336 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49
       have i₂ := eq15181
       grind)
    | exact superpose eq15181 eq49
    | exact resolve eq49 eq15181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq15347 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq891 x y
       have i₂ := eq15181
       grind)
    | exact superpose eq15181 eq891
    | (have j0 := eq891 x y
       grind)
    | exact resolve eq891 eq15181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891 eq15181
  have eq15352 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15347
       have i₂ := eq45 x
       grind)
    | exact superpose eq45 eq15347
    | exact resolve eq15347 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq15347
  have eq15362 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15336
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15336
    | exact resolve eq15336 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15336
  have eq15364 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15352
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq15352
    | exact resolve eq15352 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq15352
  have eq15370 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15364
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15364
    | exact resolve eq15364 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15364
  have eq15374 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15370
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15370
    | exact resolve eq15370 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15370
  have eq15380 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15374
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15374
    | exact resolve eq15374 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15374
  have eq15385 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15380
    | exact resolve eq15380 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15380
  have eq15386 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq15385
  have eq15392 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15386
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15386
    | exact resolve eq15386 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15386
  have eq15395 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15392
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15392
    | exact resolve eq15392 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15392
  have eq15396 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq15395
  have eq15637 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15211 eq79
    | exact resolve eq79 eq15211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq15211
  have eq15660 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq15637
    | exact resolve eq15637 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15637
  have eq15798 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15362 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq15362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15362
  have eq15799 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15798
  have eq15801 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15799
    | exact resolve eq15799 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15799
  have eq15802 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq15801
  have eq16301 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq15660
       grind)
    | exact superpose eq15660 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq15660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15660
  have eq16302 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq16301
  have eq16304 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16302
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16302
    | exact resolve eq16302 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16302
  have eq16305 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16304
  have eq17497 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq15159 eq125
    | exact resolve eq125 eq15159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq15159
  have eq17511 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17497
  have eq17531 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq17511
       grind)
    | exact superpose eq17511 eq56
    | exact resolve eq56 eq17511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17511
  have eq17553 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17531
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17531
    | exact resolve eq17531 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17531
  have eq17556 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq17553 eq30
    | exact resolve eq30 eq17553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17553
  have eq17713 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq17556
    | exact resolve eq17556 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17556
  have eq17714 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq17713
  have eq17735 : y = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq17714 eq30
    | exact resolve eq30 eq17714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17714
  have eq17923 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq17735
    | exact resolve eq17735 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17735
  have eq17945 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq17923 eq57
    | exact resolve eq57 eq17923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq18184 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) y)) = X0 ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 y
       have i₂ := eq17945
       grind)
    | exact superpose eq17945 eq14
    | exact resolve eq14 eq17945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17945
  have eq36246 : x = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18184 x y
       have i₂ := eq16305
       grind)
    | exact superpose eq16305 eq18184
    | exact resolve eq18184 eq16305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16305 eq18184
  have eq36441 : x = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq36246
  have eq36483 : x = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq36441
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36441
    | exact resolve eq36441 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36441
  have eq36612 : x = (M.op x y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq17923 eq36483
    | exact resolve eq36483 eq17923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17923 eq36483
  have eq36644 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq36612
  have eq36646 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36644
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36644
    | exact resolve eq36644 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36644
  have eq36647 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq36646
  have eq36684 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq36647 eq30
    | exact resolve eq30 eq36647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36647
  have eq36968 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq36684
    | exact resolve eq36684 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq36684
  have eq36969 : x = (M.op x y) ∨ x = y := by grind
  clear eq36968
  have eq36989 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq36969 eq21
    | exact resolve eq21 eq36969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36997 : y = (k y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq36969 eq92
    | exact resolve eq92 eq36969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq37104 : y = (k y x) ∨ x = y := by grind
  clear eq36997
  have eq37172 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq36989
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36989
    | exact resolve eq36989 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36989
  have eq37191 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq37172 eq27
    | exact resolve eq27 eq37172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37269 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq37172 eq15396
    | exact resolve eq15396 eq37172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15396
  have eq37271 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq37172 eq15802
    | exact resolve eq15802 eq37172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15802
  have eq37298 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq37271
  have eq37300 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq37269
  have eq37311 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq37298
       have r₂ := eq28
       grind)
    | exact resolve eq37298 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37298
  have eq37313 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq37300
       have r₂ := eq28
       grind)
    | exact resolve eq37300 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37300
  have eq37476 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq111
       have i₂ := eq37104
       grind)
    | exact superpose eq37104 eq111
    | exact resolve eq111 eq37104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq37104
  have eq37511 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq37476
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37476
    | exact resolve eq37476 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37476
  have eq37754 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq37511 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq37511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37511
  have eq37770 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq37754
    | exact resolve eq37754 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37754
  have eq42030 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq37313 eq66
    | exact resolve eq66 eq37313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq37313
  have eq100641 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq37311 eq42030
    | exact resolve eq42030 eq37311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42030
  have eq100675 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq100641
  have eq100687 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq100675 eq56
    | exact resolve eq56 eq100675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq100675
  have eq176503 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq37172 eq37770
    | exact resolve eq37770 eq37172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37172 eq37770
  have eq176546 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq176503
  have eq285257 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq176546 eq37311
    | exact resolve eq37311 eq176546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37311 eq176546
  have eq285303 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq285257
  have eq285403 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq285303 eq100687
    | exact resolve eq100687 eq285303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100687 eq285303
  have eq285412 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq285403
  have eq285859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq285412 eq37191
    | exact resolve eq37191 eq285412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37191 eq285412
  have eq285905 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq285859
  have eq285909 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq285905
       have r₂ := eq28
       grind)
    | exact resolve eq285905 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285905
  have eq285914 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq285909 eq30
    | exact resolve eq30 eq285909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq285909
  have eq286745 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq285914
    | exact resolve eq285914 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq285914
  have eq287007 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq286745 eq36969
    | exact resolve eq36969 eq286745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36969 eq286745
  have eq287554 : x = y := by grind
  clear eq287007
  have eq287847 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq287554
       grind)
    | exact superpose eq287554 eq19
    | exact resolve eq19 eq287554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq287848 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq287554
       grind)
    | exact superpose eq287554 eq25
    | exact resolve eq25 eq287554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq287554
  have eq288203 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq287848
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq287848
    | exact resolve eq287848 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq287848
  have eq288235 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq288203 eq27
    | exact resolve eq27 eq288203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq288203
  have eq289534 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq288235 eq103
    | exact resolve eq103 eq288235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq288235
  have eq290012 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq289534
       have i₂ := eq287847
       grind)
    | exact superpose eq287847 eq289534
    | exact resolve eq289534 eq287847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287847 eq289534
  have eq291358 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq290012 eq15
    | exact resolve eq15 eq290012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290012
  have eq291774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq291358
    | exact resolve eq291358 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq291358
  have eq291893 : False := by grind
  exact eq291893
