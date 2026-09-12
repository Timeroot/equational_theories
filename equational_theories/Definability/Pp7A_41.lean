import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxx_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq78 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq92
    | exact resolve eq92 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
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
  have eq159 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq136 eq16
    | exact resolve eq16 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq222 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq523 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq533 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq523 X0
       grind)
    | exact superpose eq523 eq14
    | exact resolve eq14 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq820 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq533 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq533
    | exact resolve eq533 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq53 eq533
    | exact resolve eq533 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq824 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54 eq533
    | exact resolve eq533 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq533
  have eq872 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq890 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq872 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq892 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq890 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq890 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq890 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq890 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq902 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq892 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq892
    | (have j0 := eq892 X0 X1
       grind)
    | exact resolve eq892 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq912 : x ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq822 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6386 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq78 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78
    | (have j0 := eq78 x
       grind)
    | exact resolve eq78 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq6430 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6386
  have eq6435 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6430
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq6430
    | exact resolve eq6430 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq6430
  have eq6453 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6435
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6435 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6435
  have eq6457 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6453 eq49
    | exact resolve eq49 eq6453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq6453
  have eq6899 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq137
    | (have j0 := eq137 (M.op x y)
       grind)
    | exact resolve eq137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq6924 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6899
  have eq6927 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq136 eq6924
    | exact resolve eq6924 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq6924
  have eq6959 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6927
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6927 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6927
  have eq6995 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq6959 eq159
    | exact resolve eq159 eq6959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq6959
  have eq9193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq9193
    | exact resolve eq9193 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9193
  have eq9205 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq9194
       have r₂ := eq27
       grind)
    | exact resolve eq9194 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9194
  have eq9207 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq9205
    | exact resolve eq9205 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9205
  have eq9395 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9207 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq9207
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq9207
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq9207
       grind)
    | exact resolve eq13 eq9207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9396 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq9207 eq14
    | exact resolve eq14 eq9207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9419 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9207 eq820
    | exact resolve eq820 eq9207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9420 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq9395
  have eq9433 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9396 x
       have i₂ := eq820 sF3 x
       grind)
    | exact superpose eq820 eq9396
    | exact resolve eq9396 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9396
  have eq10010 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9420 eq95
    | exact resolve eq95 eq9420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq9420
  have eq10018 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10010
  have eq10652 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9419 eq9433
    | exact resolve eq9433 eq9419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9419
  have eq10707 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq10652
  have eq10948 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq10707 eq9207
    | exact resolve eq9207 eq10707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9207
  have eq10949 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq10707 eq9433
    | exact resolve eq9433 eq10707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9433 eq10707
  have eq10986 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq10949
  have eq10987 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq10948
  have eq10994 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq10987
       grind)
    | exact superpose eq10987 eq14
    | exact resolve eq14 eq10987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11046 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq10994 X0
       have i₂ := eq820 y X0
       grind)
    | exact superpose eq820 eq10994
    | exact resolve eq10994 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10994
  have eq12842 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq10986 eq10018
    | exact resolve eq10018 eq10986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10018 eq10986
  have eq12901 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12842
  have eq12942 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq12901
       grind)
    | exact superpose eq12901 eq14
    | exact resolve eq14 eq12901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12977 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq820 y x
       have i₂ := eq12901
       grind)
    | exact superpose eq12901 eq820
    | exact resolve eq820 eq12901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12997 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12942 X0
       have i₂ := eq820 y X0
       grind)
    | exact superpose eq820 eq12942
    | exact resolve eq12942 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12942
  have eq13548 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq12977
       grind)
    | exact superpose eq12977 eq14
    | exact resolve eq14 eq12977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12977
  have eq13601 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13548 X0
       have i₂ := eq820 y X0
       grind)
    | exact superpose eq820 eq13548
    | exact resolve eq13548 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq13548
  have eq13825 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11046 x
       have i₂ := eq10987
       grind)
    | exact superpose eq10987 eq11046
    | exact resolve eq11046 eq10987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11046
  have eq13885 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq13825
  have eq13904 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10987
       have i₂ := eq13885
       grind)
    | exact superpose eq13885 eq10987
    | exact resolve eq10987 eq13885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10987 eq13885
  have eq13945 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq13904
  have eq13968 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13945 eq222
    | exact resolve eq222 eq13945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq13993 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13945 eq824
    | exact resolve eq824 eq13945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16310 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12997 x
       have i₂ := eq12901
       grind)
    | exact superpose eq12901 eq12997
    | exact resolve eq12997 eq12901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12901 eq12997
  have eq16372 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16310
  have eq24248 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13601 x
       have i₂ := eq16372
       grind)
    | exact superpose eq16372 eq13601
    | exact resolve eq13601 eq16372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13601 eq16372
  have eq24320 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24248
  have eq24328 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24320
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24320
    | exact resolve eq24320 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24320
  have eq24364 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24328 eq824
    | exact resolve eq824 eq24328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824 eq24328
  have eq24408 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24364 eq6457
    | exact resolve eq6457 eq24364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6457 eq24364
  have eq24524 : x = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq24408
    | exact resolve eq24408 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24408
  have eq25004 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq24524
       grind)
    | exact superpose eq24524 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq24524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24524
  have eq25026 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq25004
  have eq28748 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13993 eq13968
    | exact resolve eq13968 eq13993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13968 eq13993
  have eq28811 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq28748
  have eq28820 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq28811
    | exact resolve eq28811 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28811
  have eq28867 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28820 eq13945
    | exact resolve eq13945 eq28820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13945 eq28820
  have eq28894 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq28867
  have eq28912 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28894 eq29
    | exact resolve eq29 eq28894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28894
  have eq29071 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq28912
    | exact resolve eq28912 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28912
  have eq29072 : x = (M.op x y) ∨ x = y := by grind
  clear eq29071
  have eq29439 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq29072 eq20
    | exact resolve eq20 eq29072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29523 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29072 eq822
    | exact resolve eq822 eq29072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq29598 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq29439
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29439
    | exact resolve eq29439 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29439
  have eq29850 : x ≠ x ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq29523
       grind)
    | exact superpose eq29523 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq29523
       grind)
    | exact resolve eq13 eq29523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29523
  have eq29901 : x = (k x x) ∨ x = y := by grind
  clear eq29850
  have eq31438 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq902 x x
       have i₂ := eq29901
       grind)
    | exact superpose eq29901 eq902
    | (have j0 := eq902 x x
       grind)
    | exact resolve eq902 eq29901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29901
  have eq31439 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq31438
  have eq31440 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq31439
  have eq31459 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq31440
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31440
    | exact resolve eq31440 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31440
  have eq32879 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq29598 eq31459
    | exact resolve eq31459 eq29598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29598 eq31459
  have eq32971 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq32879
  have eq33865 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq32971 eq6995
    | exact resolve eq6995 eq32971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6995 eq32971
  have eq33965 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30 eq33865
    | exact resolve eq33865 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33865
  have eq35579 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq33965 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq33965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33965
  have eq35609 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq35579
  have eq35877 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq35609 eq213
    | exact resolve eq213 eq35609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq35609
  have eq36126 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq29072 eq35877
    | exact resolve eq35877 eq29072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35877
  have eq36188 : y = (M.op x y) ∨ x = y := by grind
  clear eq36126
  have eq36190 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq36188
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36188
    | exact resolve eq36188 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36188
  have eq36290 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq36190 eq29072
    | exact resolve eq29072 eq36190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29072 eq36190
  have eq36301 : x = y := by grind
  clear eq36290
  have eq36400 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq36301
       grind)
    | exact superpose eq36301 eq18
    | exact resolve eq18 eq36301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq36401 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq36301
       grind)
    | exact superpose eq36301 eq24
    | exact resolve eq24 eq36301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq36552 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq36401
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36401
    | exact resolve eq36401 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36401
  have eq36590 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq36552 eq26
    | exact resolve eq26 eq36552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq36552
  have eq36769 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25026
       have i₂ := eq36400
       grind)
    | exact superpose eq36400 eq25026
    | exact resolve eq25026 eq36400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25026
  have eq36855 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq36769
  have eq36877 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq36855
       have i₂ := eq36301
       grind)
    | exact superpose eq36301 eq36855
    | exact resolve eq36855 eq36301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36301 eq36855
  have eq36878 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq36877
  have eq37441 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36878 eq28
    | exact resolve eq28 eq36878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq36878
  have eq37678 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq37441
    | exact resolve eq37441 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq37441
  have eq37679 : x = (M.op x y) := by grind
  clear eq37678
  have eq37774 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq37679 eq20
    | exact resolve eq20 eq37679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq37859 : x ≠ x ∨ (k x x) = (M.op x x) := by
    first
    | exact superpose eq37679 eq912
    | (have r₁ := eq912
       have r₂ := eq37679
       grind)
    | exact resolve eq912 eq37679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq37872 : (k x x) = (M.op x x) := by grind
  clear eq37859
  have eq37879 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq37872
       have i₂ := eq36400
       grind)
    | exact superpose eq36400 eq37872
    | exact resolve eq37872 eq36400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36400 eq37872
  have eq37953 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37774
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37774
    | exact resolve eq37774 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37774
  have eq37955 : x = (k x x) := by
    first
    | exact superpose eq37679 eq37879
    | exact resolve eq37879 eq37679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37679 eq37879
  have eq38429 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq902 x x
       have i₂ := eq37955
       grind)
    | exact superpose eq37955 eq902
    | (have j0 := eq902 x x
       grind)
    | exact resolve eq902 eq37955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902 eq37955
  have eq38434 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq38429
  have eq38435 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq38434
  have eq38456 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq38435
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38435
    | exact resolve eq38435 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq38435
  have eq38480 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36590 eq38456
    | exact resolve eq38456 eq36590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36590 eq38456
  have eq38501 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37953 eq38480
    | exact resolve eq38480 eq37953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37953 eq38480
  have eq38522 : False := by grind
  exact eq38522

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxx_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq84 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq96 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
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
  have eq159 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq136 eq16
    | exact resolve eq16 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq222 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq637 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq648 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq637 X0
       grind)
    | exact superpose eq637 eq14
    | exact resolve eq14 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq862 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq878 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq862 X0 X1
       have j1 := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq862 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq862 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq862 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq888 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq878 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq878
    | (have j0 := eq878 X0 X1
       grind)
    | exact resolve eq878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq904 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq648 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq648
    | exact resolve eq648 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq906 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq53 eq648
    | exact resolve eq648 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq908 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54 eq648
    | exact resolve eq648 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq648
  have eq924 : x ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq906 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6411 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq96 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq96
    | (have j0 := eq96 x
       grind)
    | exact resolve eq96 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq6455 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6411
  have eq6460 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6455
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq6455
    | exact resolve eq6455 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq6455
  have eq6478 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6460
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6460 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6460
  have eq6482 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6478 eq49
    | exact resolve eq49 eq6478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq6478
  have eq6835 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq137
    | (have j0 := eq137 (M.op x y)
       grind)
    | exact resolve eq137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq6860 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6835
  have eq6863 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq136 eq6860
    | exact resolve eq6860 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq6860
  have eq6895 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6863
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6863 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6863
  have eq6931 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq6895 eq159
    | exact resolve eq159 eq6895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq6895
  have eq10501 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq10502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq10501
    | exact resolve eq10501 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10501
  have eq10513 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq10502
       have r₂ := eq27
       grind)
    | exact resolve eq10502 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10502
  have eq10515 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq10513
    | exact resolve eq10513 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10513
  have eq10517 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq10515 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq10515
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq10515
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq10515
       grind)
    | exact resolve eq12 eq10515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10515
  have eq10550 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq10517
  have eq10566 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq10550
    | exact resolve eq10550 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10550
  have eq10567 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq10566
  have eq10886 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq10567 eq84
    | exact resolve eq84 eq10567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq10567
  have eq10902 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq10886
    | exact resolve eq10886 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10886
  have eq11163 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq10902
       grind)
    | exact superpose eq10902 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq10902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10902
  have eq11164 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11163
  have eq11166 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11164
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11164
    | exact resolve eq11164 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11164
  have eq11167 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11166
  have eq11179 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq11167
       grind)
    | exact superpose eq11167 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11167
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11167
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11167
       grind)
    | exact resolve eq12 eq11167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11214 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq904 y x
       have i₂ := eq11167
       grind)
    | exact superpose eq11167 eq904
    | exact resolve eq904 eq11167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11167
  have eq11216 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11179
  have eq11234 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11216
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11216
    | exact resolve eq11216 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11216
  have eq11235 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11234
  have eq11474 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq11214
       grind)
    | exact superpose eq11214 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq11214
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq11214
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq11214
       grind)
    | exact resolve eq13 eq11214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11214
  have eq11511 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11474
  have eq12233 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq873 y x
       have i₂ := eq11235
       grind)
    | exact superpose eq11235 eq873
    | (have j0 := eq873 y x
       grind)
    | exact resolve eq873 eq11235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11235
  have eq12236 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12233
  have eq12238 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12236
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12236
    | exact resolve eq12236 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12236
  have eq12246 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12238
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12238
    | exact resolve eq12238 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12238
  have eq12249 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12246
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12246
    | exact resolve eq12246 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12246
  have eq12250 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12249
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12249
    | exact resolve eq12249 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12249
  have eq12251 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12250
    | exact resolve eq12250 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12250
  have eq12252 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12251
  have eq12264 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq873 y y
       have i₂ := eq11511
       grind)
    | exact superpose eq11511 eq873
    | (have j0 := eq873 y y
       grind)
    | exact resolve eq873 eq11511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq11511
  have eq12267 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12264
  have eq12268 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12267
  have eq12272 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12268
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12268
    | exact resolve eq12268 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12268
  have eq13004 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12252 eq14
    | exact resolve eq14 eq12252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13059 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13004 x
       have i₂ := eq904 sF3 x
       grind)
    | exact superpose eq904 eq13004
    | exact resolve eq13004 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13004
  have eq13074 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq12272 eq14
    | exact resolve eq14 eq12272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13127 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13074 x
       have i₂ := eq904 sF3 x
       grind)
    | exact superpose eq904 eq13074
    | exact resolve eq13074 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904 eq13074
  have eq15693 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12272 eq13059
    | exact resolve eq13059 eq12272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12272 eq13059
  have eq15757 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15693
  have eq15773 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15757 eq12252
    | exact resolve eq12252 eq15757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12252
  have eq15818 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq15773
  have eq18643 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15757 eq13127
    | exact resolve eq13127 eq15757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13127 eq15757
  have eq18715 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18643
  have eq18718 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18715
    | exact resolve eq18715 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18715
  have eq18767 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18718
  have eq18779 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18767
       have r₂ := eq15818
       grind)
    | exact resolve eq18767 eq15818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15818 eq18767
  have eq19720 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18779 eq222
    | exact resolve eq222 eq18779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq19749 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18779 eq908
    | exact resolve eq908 eq18779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq19791 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19749 eq6482
    | exact resolve eq6482 eq19749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6482
  have eq19904 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq19791
    | exact resolve eq19791 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19791
  have eq21132 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq19904
       grind)
    | exact superpose eq19904 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq19904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19904
  have eq21149 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq21132
  have eq23319 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19749 eq19720
    | exact resolve eq19720 eq19749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19720 eq19749
  have eq23372 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23319
  have eq23378 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq23372
    | exact resolve eq23372 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23372
  have eq23431 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23378 eq18779
    | exact resolve eq18779 eq23378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18779 eq23378
  have eq23436 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq23431
  have eq23859 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23436 eq29
    | exact resolve eq29 eq23436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq23436
  have eq24037 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq23859
    | exact resolve eq23859 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq23859
  have eq24448 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq24037 eq20
    | exact resolve eq20 eq24037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24532 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq24037 eq906
    | exact resolve eq906 eq24037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq24604 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq24448
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24448
    | exact resolve eq24448 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24448
  have eq26066 : x ≠ x ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq24532
       grind)
    | exact superpose eq24532 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq24532
       grind)
    | exact resolve eq13 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24532
  have eq26113 : x = (k x x) ∨ x = y := by grind
  clear eq26066
  have eq27914 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq888 x x
       have i₂ := eq26113
       grind)
    | exact superpose eq26113 eq888
    | (have j0 := eq888 x x
       grind)
    | exact resolve eq888 eq26113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26113
  have eq27915 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq27914
  have eq27916 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq27915
  have eq27930 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq27916
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27916
    | exact resolve eq27916 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27916
  have eq28428 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq24604 eq27930
    | exact resolve eq27930 eq24604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24604 eq27930
  have eq28516 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq28428
  have eq29905 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq28516 eq6931
    | exact resolve eq6931 eq28516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6931 eq28516
  have eq29996 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30 eq29905
    | exact resolve eq29905 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29905
  have eq30080 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq29996 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq29996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29996
  have eq30103 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq30080
  have eq30531 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq30103 eq213
    | exact resolve eq213 eq30103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq30103
  have eq30624 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq24037 eq30531
    | exact resolve eq30531 eq24037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30531
  have eq30680 : y = (M.op x y) ∨ x = y := by grind
  clear eq30624
  have eq30682 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq30680
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq30680
    | exact resolve eq30680 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30680
  have eq30778 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq30682 eq24037
    | exact resolve eq24037 eq30682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24037 eq30682
  have eq30789 : x = y := by grind
  clear eq30778
  have eq30884 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq30789
       grind)
    | exact superpose eq30789 eq18
    | exact resolve eq18 eq30789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq30885 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq30789
       grind)
    | exact superpose eq30789 eq24
    | exact resolve eq24 eq30789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq30789
  have eq31025 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq30885
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30885
    | exact resolve eq30885 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30885
  have eq32454 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31025 eq26
    | exact resolve eq26 eq31025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq31025
  have eq32646 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21149
       have i₂ := eq30884
       grind)
    | exact superpose eq30884 eq21149
    | exact resolve eq21149 eq30884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21149
  have eq32728 : x = (M.op x y) := by grind
  clear eq32646
  have eq35213 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq32728 eq20
    | exact resolve eq20 eq32728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq35298 : x ≠ x ∨ (k x x) = (M.op x x) := by
    first
    | exact superpose eq32728 eq924
    | (have r₁ := eq924
       have r₂ := eq32728
       grind)
    | exact resolve eq924 eq32728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq35310 : (k x x) = (M.op x x) := by grind
  clear eq35298
  have eq35316 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq35310
       have i₂ := eq30884
       grind)
    | exact superpose eq30884 eq35310
    | exact resolve eq35310 eq30884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30884 eq35310
  have eq35390 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq35213
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35213
    | exact resolve eq35213 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35213
  have eq35392 : x = (k x x) := by
    first
    | exact superpose eq32728 eq35316
    | exact resolve eq35316 eq32728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32728 eq35316
  have eq37781 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq35390 eq32454
    | exact resolve eq32454 eq35390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32454
  have eq38005 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq888 x x
       have i₂ := eq35392
       grind)
    | exact superpose eq35392 eq888
    | (have j0 := eq888 x x
       grind)
    | exact resolve eq888 eq35392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq35392
  have eq38010 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq38005
  have eq38011 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq38010
  have eq38028 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq38011
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38011
    | exact resolve eq38011 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq38011
  have eq38051 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq35390 eq38028
    | exact resolve eq38028 eq35390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35390 eq38028
  have eq38071 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37781 eq38051
    | exact resolve eq38051 eq37781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37781 eq38051
  have eq38091 : False := by grind
  exact eq38091

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxx_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq188 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq195 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq190 eq16
    | exact resolve eq16 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq183 eq188
    | exact resolve eq188 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq561 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq556
       grind)
    | exact superpose eq556 eq16
    | exact resolve eq16 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq568 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq190 eq195
    | exact resolve eq195 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq573 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq568 eq16
    | exact resolve eq16 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq581 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq561 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq561
    | exact resolve eq561 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq631 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq573 (M.op sF3 x)
       have i₂ := eq16 sF3 sF3 x
       grind)
    | exact superpose eq16 eq573
    | exact resolve eq573 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq831 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq631
       grind)
    | exact superpose eq631 eq40
    | exact resolve eq40 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq631
  have eq832 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq831
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq831
    | exact resolve eq831 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq834 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq832
    | exact resolve eq832 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq906 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq199
    | exact resolve eq199 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq931 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq906 X0
       grind)
    | exact superpose eq906 eq16
    | exact resolve eq16 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq990 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq931 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq931
    | exact resolve eq931 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq994 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq177 eq931
    | exact resolve eq931 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq998 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq178 eq931
    | exact resolve eq931 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq931
  have eq1748 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq834 eq633
    | exact resolve eq633 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq834
  have eq1755 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1748
       have r₂ := eq27
       grind)
    | exact resolve eq1748 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748
  have eq1763 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1755 eq16
    | exact resolve eq16 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1770 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1755 eq990
    | exact resolve eq990 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1776 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq747 eq1763
    | exact resolve eq1763 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq1763
  have eq2265 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1770 eq1776
    | exact resolve eq1776 eq1770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770 eq1776
  have eq2287 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq2265
  have eq2297 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2287 eq1755
    | exact resolve eq1755 eq2287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755 eq2287
  have eq2313 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq2297
  have eq2323 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq2313
       grind)
    | exact superpose eq2313 eq16
    | exact resolve eq16 eq2313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2331 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq990 y x
       have i₂ := eq2313
       grind)
    | exact superpose eq2313 eq990
    | exact resolve eq990 eq2313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq2338 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2323 X0
       have i₂ := eq581 X0
       grind)
    | exact superpose eq581 eq2323
    | exact resolve eq2323 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq2323
  have eq3125 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2338 y
       have i₂ := eq2331
       grind)
    | exact superpose eq2331 eq2338
    | exact resolve eq2338 eq2331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331 eq2338
  have eq3154 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq3125
  have eq3175 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2313
       have i₂ := eq3154
       grind)
    | exact superpose eq3154 eq2313
    | exact resolve eq2313 eq3154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2313 eq3154
  have eq3196 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq3175
  have eq3221 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3196 eq190
    | exact resolve eq190 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq3237 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3196 eq998
    | exact resolve eq998 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq3255 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3237 eq3221
    | exact resolve eq3221 eq3237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3221 eq3237
  have eq3259 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq3255
    | exact resolve eq3255 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3255
  have eq3260 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3196 eq3259
    | exact resolve eq3259 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196 eq3259
  have eq3261 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq3260
  have eq3263 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq3261 eq31
    | exact resolve eq31 eq3261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3261
  have eq3333 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3263
    | exact resolve eq3263 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3263
  have eq3334 : x = (M.op x y) ∨ x = y := by grind
  clear eq3333
  have eq3336 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq3334
       grind)
    | exact superpose eq3334 eq18
    | exact resolve eq18 eq3334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3348 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq994
       have i₂ := eq3334
       grind)
    | exact superpose eq3334 eq994
    | exact resolve eq994 eq3334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq3418 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq3348 eq183
    | exact resolve eq183 eq3348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq3348
  have eq3440 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3336 eq3418
    | exact resolve eq3418 eq3336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336 eq3418
  have eq3489 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq3440
  have eq3490 : x = y := by
    first
    | (have r₁ := eq3489
       have r₂ := eq3334
       grind)
    | exact resolve eq3489 eq3334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334 eq3489
  have eq3495 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3490
       grind)
    | exact superpose eq3490 eq18
    | exact resolve eq18 eq3490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3496 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3490
       grind)
    | exact superpose eq3490 eq24
    | exact resolve eq24 eq3490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3490
  have eq3551 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3496
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3496
    | exact resolve eq3496 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3496
  have eq3553 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3551 eq26
    | exact resolve eq26 eq3551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3551
  have eq3631 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq3495
       grind)
    | exact superpose eq3495 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq3495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3633 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq3495
       grind)
    | exact superpose eq3495 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq3495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3495
  have eq3649 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq3631
  have eq3652 : (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq3649
       have r₂ := eq3633
       grind)
    | exact resolve eq3649 eq3633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3633 eq3649
  have eq4701 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3553 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq3553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4703 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3553 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq3553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3553
  have eq4723 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4701
  have eq4728 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq4723
       have r₂ := eq4703
       grind)
    | exact resolve eq4723 eq4703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4703 eq4723
  have eq4768 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3652
       grind)
    | exact superpose eq3652 eq39
    | exact resolve eq39 eq3652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq3652
  have eq4780 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4768
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4768
    | exact resolve eq4768 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4768
  have eq4782 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4728 eq4780
    | exact resolve eq4780 eq4728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4728 eq4780
  have eq4784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4782
    | exact resolve eq4782 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4782
  have eq4786 : False := by grind
  exact eq4786

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq17
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq94 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X4) X3) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X0 X1) X0 X1 (M.op (M.op X0 (M.op X0 X1)) X2)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 (M.op X0 X1)) X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq128 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 x y
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 x y
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq66 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq66 X0 X1
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq66 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq66 X0 X1
       grind)
    | exact resolve eq13 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq139 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq132 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq132 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq132 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq140 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq131 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq131 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq143 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq139
    | (have j0 := eq139 X0 X1
       grind)
    | exact resolve eq139 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq144 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq140
    | (have j0 := eq140 X0 X1
       grind)
    | exact resolve eq140 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq373 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128
       have i₂ := eq55 x y
       grind)
    | exact superpose eq55 eq128
    | (have j1 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq128 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq128
  have eq376 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq373
  have eq378 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq376
       grind)
    | exact superpose eq376 eq9
    | exact resolve eq9 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq899 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq94 X0 X1 X2 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq94
    | exact resolve eq94 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq920 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq899 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq899
    | exact resolve eq899 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq2095 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq143 (τ X1) (τ X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq143
    | (have j0 := eq143 (τ X0) (τ X1)
       grind)
    | exact resolve eq143 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq143
  have eq2113 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2095 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2095
    | (have j0 := eq2095 X0 X1
       grind)
    | exact resolve eq2095 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2095
  have eq2120 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2113 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2113
    | (have j0 := eq2113 X0 X1
       grind)
    | exact resolve eq2113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113
  have eq2126 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2120 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2120
    | (have j0 := eq2120 X0 X1
       grind)
    | exact resolve eq2120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2120
  have eq2131 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2126 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2126
    | (have j0 := eq2126 X0 X1
       grind)
    | exact resolve eq2126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126
  have eq2136 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2131 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2131
    | (have j0 := eq2131 X0 X1
       grind)
    | exact resolve eq2131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131
  have eq2141 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2136 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2136
    | (have j0 := eq2136 X0 X1
       grind)
    | exact resolve eq2136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2136
  have eq2146 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2141 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2141
    | (have j0 := eq2141 X0 X1
       grind)
    | exact resolve eq2141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141
  have eq2375 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq378 x
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq378
    | exact resolve eq378 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2500 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 x x X0
       have i₂ := eq2375
       grind)
    | exact superpose eq2375 eq9
    | exact resolve eq9 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq3599 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq100 x X0 x
       have i₂ := eq2500 X0
       grind)
    | exact superpose eq2500 eq100
    | exact resolve eq100 eq2500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq2500
  have eq4853 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq920 (σ x) (σ y)
       have i₂ := eq3599 X0
       grind)
    | exact superpose eq3599 eq920
    | (have j1 := eq3599 X0
       grind)
    | exact resolve eq920 eq3599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3599
  have eq6170 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq4853 X0
       grind)
    | exact superpose eq4853 eq12
    | (have j1 := eq4853 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq4853 X0
       grind)
    | exact resolve eq12 eq4853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4853
  have eq6231 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6170 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6170
  have eq6267 : ∀ X0 : G, (σ x) = (σ (k x x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq6231 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq6231
    | (have j0 := eq6231 X0
       grind)
    | exact resolve eq6231 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6231
  have eq6307 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq6267 X0
       grind)
    | exact superpose eq6267 eq10
    | (have j1 := eq6267 X0
       grind)
    | exact resolve eq10 eq6267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6267
  have eq6365 : ∀ X0 : G, x = (k x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq6307 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6307
    | (have j0 := eq6307 X0
       grind)
    | exact resolve eq6307 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6307
  have eq6387 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq2146 x x
       have i₂ := eq6365 X0
       grind)
    | exact superpose eq6365 eq2146
    | (have j0 := eq2146 x x
       have j1 := eq6365 X0
       grind)
    | (have r₁ := eq2146 x x
       have r₂ := eq6365 X0
       grind)
    | exact resolve eq2146 eq6365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6365
  have eq6388 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6387 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6387
  have eq6389 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6388 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6388
  have eq6408 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ x = (M.op (M.op x X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x x X0
       have i₂ := eq6389 X1
       grind)
    | exact superpose eq6389 eq9
    | (have j1 := eq6389 (M.op x X0)
       grind)
    | exact resolve eq9 eq6389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6389
  have eq6506 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ x = (M.op (M.op x X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq6408 X0 X1
       have i₂ := eq920 x X0
       grind)
    | (have i₁ := eq6408 X0 X1
       have i₂ := eq920 x (M.op x X0)
       grind)
    | exact superpose eq920 eq6408
    | (have j0 := eq6408 X0 X0
       grind)
    | exact resolve eq6408 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6408
  have eq6990 : ∀ X0 : G, x ≠ x ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6506 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6506
  have eq6991 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6990 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6990
  have eq7021 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq378 X0
       have i₂ := eq6991 X0
       grind)
    | exact superpose eq6991 eq378
    | exact resolve eq378 eq6991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq7418 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq920 (σ x) (σ y)
       have i₂ := eq7021 X0
       grind)
    | exact superpose eq7021 eq920
    | (have j1 := eq7021 X0
       grind)
    | exact resolve eq920 eq7021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq7021
  have eq7732 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq7418 X0
       grind)
    | exact superpose eq7418 eq12
    | (have j1 := eq7418 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq7418 X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq7418 x
       grind)
    | exact resolve eq12 eq7418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7418
  have eq7793 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7732 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7732
  have eq7829 : ∀ X0 : G, (σ x) = (σ (k x x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7793 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq7793
    | (have j0 := eq7793 X0
       grind)
    | exact resolve eq7793 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7793
  have eq8065 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq7829 X0
       grind)
    | exact superpose eq7829 eq10
    | (have j1 := eq7829 X0
       grind)
    | exact resolve eq10 eq7829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7829
  have eq8126 : ∀ X0 : G, x = (k x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8065 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8065
    | (have j0 := eq8065 X0
       grind)
    | exact resolve eq8065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8065
  have eq8278 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2146 x x
       have i₂ := eq8126 X0
       grind)
    | exact superpose eq8126 eq2146
    | (have j0 := eq2146 x x
       have j1 := eq8126 x
       grind)
    | (have r₁ := eq2146 x x
       have r₂ := eq8126 X0
       grind)
    | exact resolve eq2146 eq8126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146 eq8126
  have eq8279 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8278 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8278
  have eq8280 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8279 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8279
  have eq8505 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq8280 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8280
  have eq8506 : x = (M.op x x) := by grind
  clear eq8505
  have eq8766 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq8506
       grind)
    | exact superpose eq8506 eq9
    | exact resolve eq9 eq8506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8767 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq8506
       grind)
    | exact superpose eq8506 eq12
    | (have r₁ := eq12 x x
       have r₂ := eq8506
       grind)
    | exact resolve eq12 eq8506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8506
  have eq8829 : x = (k x x) := by grind
  clear eq8767
  have eq8881 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8766 X0
       have i₂ := eq6991 X0
       grind)
    | exact superpose eq6991 eq8766
    | exact resolve eq8766 eq6991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6991 eq8766
  have eq9096 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq144 x x
       have i₂ := eq8829
       grind)
    | exact superpose eq8829 eq144
    | exact resolve eq144 eq8829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq8829
  have eq9114 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq9096
  have eq9310 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 x X0
       have i₂ := eq8881 X0
       grind)
    | exact superpose eq8881 eq9
    | exact resolve eq9 eq8881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9486 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9310 X0 X1
       have i₂ := eq8881 X1
       grind)
    | exact superpose eq8881 eq9310
    | exact resolve eq9310 eq8881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9310
  have eq12728 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ x)
       have i₂ := eq9114
       grind)
    | exact superpose eq9114 eq9
    | exact resolve eq9 eq9114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9114
  have eq12844 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12728 X0
       have i₂ := eq9486 X0 (σ x)
       grind)
    | exact superpose eq9486 eq12728
    | exact resolve eq12728 eq9486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9486 eq12728
  have eq12923 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12844 (σ y)
       grind)
    | exact superpose eq12844 eq16
    | exact resolve eq16 eq12844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12844
  have eq13113 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq12923
       have i₂ := eq8881 y
       grind)
    | exact superpose eq8881 eq12923
    | exact resolve eq12923 eq8881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8881 eq12923
  have eq13114 : False := by grind
  exact eq13114

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then Y else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_y_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq50 : x ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq59 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq60 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74
    | exact resolve eq74 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq81
    | exact resolve eq81 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq87 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq101 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq140 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq222 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 (σ y)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq240 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ≠ X0 ∨ (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (k X0 (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq60 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq427 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq436 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq427 X0
       grind)
    | exact superpose eq427 eq14
    | exact resolve eq14 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X0) X1
       have i₂ := eq427 X0
       grind)
    | exact superpose eq427 eq14
    | exact resolve eq14 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq813 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq69 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq829 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq813 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq831 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq829 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq829 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq829 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq829 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq841 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq831 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq831
    | (have j0 := eq831 X0 X1
       grind)
    | exact resolve eq831 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq892 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq436 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq436
    | exact resolve eq436 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq59 eq436
    | exact resolve eq436 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq896 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60 eq436
    | exact resolve eq436 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq436
  have eq912 : x ≠ (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq894 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq892 X0 X1
       grind)
    | exact superpose eq892 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq84 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7612 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq7611
    | exact resolve eq7611 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7611
  have eq7623 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq7612
       have r₂ := eq27
       grind)
    | exact resolve eq7612 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7612
  have eq7625 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq7623
    | exact resolve eq7623 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7623
  have eq7628 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq7625 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq7625
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq7625
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq7625
       grind)
    | exact resolve eq13 eq7625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7625
  have eq7651 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq7628
  have eq7851 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq7651 eq55
    | exact resolve eq55 eq7651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq7852 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq7651 eq84
    | exact resolve eq84 eq7651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7651
  have eq7860 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7852
  have eq7868 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq7851
    | exact resolve eq7851 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7851
  have eq7871 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq7868
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq7868
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq7868
       have r₂ := eq13 x y
       grind)
    | exact resolve eq7868 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7868
  have eq7873 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq7871
       grind)
    | exact superpose eq7871 eq44
    | exact resolve eq44 eq7871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq7880 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq7871
       grind)
    | exact superpose eq7871 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq7871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7871
  have eq7881 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7880
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7880
    | exact resolve eq7880 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7880
  have eq7888 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7873
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7873
    | exact resolve eq7873 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7873
  have eq7890 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7881
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7881
    | exact resolve eq7881 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7881
  have eq7891 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7890
  have eq7906 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7888 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq7888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7888
  have eq7909 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7906
    | exact resolve eq7906 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7906
  have eq7920 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7909
    | exact resolve eq7909 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7909
  have eq7921 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7920
  have eq7926 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq7860
       grind)
    | exact superpose eq7860 eq14
    | exact resolve eq14 eq7860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7945 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq892 y x
       have i₂ := eq7860
       grind)
    | exact superpose eq7860 eq892
    | exact resolve eq892 eq7860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7860
  have eq7959 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7926 X0
       have i₂ := eq892 y X0
       grind)
    | exact superpose eq892 eq7926
    | exact resolve eq7926 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7926
  have eq7966 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq7891
       grind)
    | exact superpose eq7891 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq7891
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq7891
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7891
       grind)
    | exact resolve eq12 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7891
  have eq7991 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7966
  have eq8002 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7991
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7991
    | exact resolve eq7991 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7991
  have eq8003 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8002
  have eq8006 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8003
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8003
    | exact resolve eq8003 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8003
  have eq8168 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq437 y X0
       have i₂ := eq7945
       grind)
    | exact superpose eq7945 eq437
    | exact resolve eq437 eq7945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq8173 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8168 X0
       have i₂ := eq892 y X0
       grind)
    | exact superpose eq892 eq8168
    | exact resolve eq8168 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8168
  have eq8249 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7921 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq7921
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7921
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq7921
       grind)
    | exact resolve eq12 eq7921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8270 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7921 eq892
    | exact resolve eq892 eq7921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8274 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8249
  have eq8285 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8274
    | exact resolve eq8274 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8274
  have eq8286 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8285
  have eq8289 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8286
    | exact resolve eq8286 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8286
  have eq8379 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq8006
       grind)
    | exact superpose eq8006 eq91
    | exact resolve eq91 eq8006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq8006
  have eq8393 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8379
    | exact resolve eq8379 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8379
  have eq9388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8393 eq8289
    | exact resolve eq8289 eq8393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8289 eq8393
  have eq9391 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq9388
  have eq9395 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq9391
       have r₂ := eq27
       grind)
    | exact resolve eq9391 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9391
  have eq9632 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9395 eq27
    | exact resolve eq27 eq9395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9395
  have eq12501 : ∀ X0 : G, (σ x) ≠ (k (σ x) X0) ∨ (k (σ x) X0) = (M.op (σ (τ X0)) (σ x)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq841 x (τ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq841
    | (have j0 := eq841 x (τ X0)
       grind)
    | exact resolve eq841 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq12606 : ∀ X0 : G, (σ x) ≠ (k (σ x) X0) ∨ (k (σ x) X0) = (M.op (σ (τ X0)) (σ x)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12501 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12501
    | (have j0 := eq12501 X0
       grind)
    | exact resolve eq12501 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12501
  have eq12705 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ (τ X0)) (σ x)) ∨ (σ x) ≠ (k (σ x) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12606 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12606
    | (have j0 := eq12606 X0
       grind)
    | exact resolve eq12606 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12606
  have eq12801 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) ≠ (k (σ x) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12705 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12705
    | (have j0 := eq12705 X0
       grind)
    | exact resolve eq12705 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12705
  have eq12891 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ x)) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) ≠ (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq12801 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12801
    | (have j0 := eq12801 X0
       grind)
    | exact resolve eq12801 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12801
  have eq12979 : ∀ X0 : G, (σ x) ≠ (k (σ x) X0) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12891 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12891
    | (have j0 := eq12891 X0
       grind)
    | exact resolve eq12891 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12891
  have eq14036 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7959 y
       have i₂ := eq7945
       grind)
    | exact superpose eq7945 eq7959
    | exact resolve eq7959 eq7945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7945 eq7959
  have eq14097 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14036
  have eq26148 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8173 x
       have i₂ := eq14097
       grind)
    | exact superpose eq14097 eq8173
    | exact resolve eq8173 eq14097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8173 eq14097
  have eq26230 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26148
  have eq26235 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26230
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26230
    | exact resolve eq26230 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26230
  have eq26237 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq26235
       have r₂ := eq9632
       grind)
    | exact resolve eq26235 eq9632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9632 eq26235
  have eq26243 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26237 eq51
    | (have r₁ := eq51
       have r₂ := eq26237
       grind)
    | exact resolve eq51 eq26237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq26247 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26237 eq222
    | exact resolve eq222 eq26237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26276 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26237 eq896
    | exact resolve eq896 eq26237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26291 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq26243
  have eq26616 : (σ x) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26276 eq240
    | exact resolve eq240 eq26276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26718 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq896 eq26616
    | exact resolve eq26616 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26616
  have eq26734 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq26718
       have r₂ := eq26237
       grind)
    | exact resolve eq26718 eq26237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26237 eq26718
  have eq26738 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq896 eq26734
    | exact resolve eq26734 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26734
  have eq28072 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26291 eq101
    | exact resolve eq101 eq26291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq26291
  have eq28116 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq28072
    | exact resolve eq28072 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28072
  have eq28120 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq28116
       have r₂ := eq50
       grind)
    | exact resolve eq28116 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28116
  have eq33515 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26276 eq26247
    | exact resolve eq26247 eq26276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26247 eq26276
  have eq33583 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq33515
  have eq33588 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq33583
    | exact resolve eq33583 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33583
  have eq33592 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33588 eq27
    | exact resolve eq27 eq33588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33642 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33588 eq26738
    | exact resolve eq26738 eq33588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26738 eq33588
  have eq33643 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq33642
  have eq34560 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33643 eq84
    | exact resolve eq84 eq33643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq33643
  have eq34584 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq34560
  have eq34596 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq34584
       have r₂ := eq33592
       grind)
    | exact resolve eq34584 eq33592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33592 eq34584
  have eq34850 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq34596
       grind)
    | exact superpose eq34596 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq34596
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq34596
       grind)
    | exact resolve eq12 eq34596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34596
  have eq34909 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq34850
  have eq34944 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34909
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34909
    | exact resolve eq34909 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34909
  have eq34945 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq34944
  have eq34958 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34945
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34945
    | exact resolve eq34945 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34945
  have eq35740 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28120
       have i₂ := eq34958
       grind)
    | exact superpose eq34958 eq28120
    | exact resolve eq28120 eq34958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28120 eq34958
  have eq35767 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq35740
  have eq35884 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35767 eq20
    | exact resolve eq20 eq35767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35895 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq35767 eq122
    | exact resolve eq122 eq35767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq35767
  have eq36027 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq35895 X0
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq35895
    | exact resolve eq35895 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq35895
  have eq36036 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35884
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35884
    | exact resolve eq35884 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35884
  have eq36160 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36036 eq26
    | exact resolve eq26 eq36036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36251 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36036 eq7921
    | exact resolve eq7921 eq36036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7921
  have eq36252 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36036 eq8270
    | exact resolve eq8270 eq36036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8270
  have eq36309 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq36252
  have eq36310 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq36251
  have eq36327 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq36309
       have r₂ := eq27
       grind)
    | exact resolve eq36309 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36309
  have eq36328 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq36310
       have r₂ := eq27
       grind)
    | exact resolve eq36310 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36310
  have eq36530 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36160 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq36160
       grind)
    | exact resolve eq13 eq36160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36985 : ∀ X0 : G, (k (τ (σ y)) X0) = (τ (k (σ (M.op x y)) (σ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36027 eq303
    | exact resolve eq303 eq36027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36027
  have eq37136 : ∀ X0 : G, (k (τ (σ (M.op x y))) X0) = (k (τ (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq36985 x
       have i₂ := eq303 sF1 x
       grind)
    | exact superpose eq303 eq36985
    | exact resolve eq36985 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303 eq36985
  have eq37143 : ∀ X0 : G, (k y X0) = (k (τ (σ (M.op x y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq37136
    | exact resolve eq37136 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq37136
  have eq37148 : ∀ X0 : G, (k y X0) = (k (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq37143
    | exact resolve eq37143 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq37143
  have eq39336 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36327 eq14
    | exact resolve eq14 eq36327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36327
  have eq39418 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq39336 x
       have i₂ := eq892 sF1 x
       grind)
    | exact superpose eq892 eq39336
    | exact resolve eq39336 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39336
  have eq39830 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36328 eq14
    | exact resolve eq14 eq36328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39914 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq39830 x
       have i₂ := eq892 sF1 x
       grind)
    | exact superpose eq892 eq39830
    | exact resolve eq39830 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39830
  have eq73708 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36328 eq39914
    | exact resolve eq39914 eq36328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39914
  have eq73814 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq73708
  have eq73820 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73814 eq36328
    | exact resolve eq36328 eq73814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36328
  have eq73822 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73814 eq39418
    | exact resolve eq39418 eq73814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39418 eq73814
  have eq73892 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq73822
  have eq73894 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq73820
  have eq74067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73892 eq36160
    | exact resolve eq36160 eq73892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36160
  have eq74153 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73892 eq1013
    | (have r₁ := eq1013 (σ x) (σ y)
       have r₂ := eq73892
       grind)
    | (have r₁ := eq1013 x y
       have r₂ := eq73892
       grind)
    | exact resolve eq1013 eq73892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013 eq73892
  have eq74164 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq74067
  have eq74167 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq74153
       have r₂ := eq73894
       grind)
    | exact resolve eq74153 eq73894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73894 eq74153
  have eq74171 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq74164
       have r₂ := eq27
       grind)
    | exact resolve eq74164 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74164
  have eq74173 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq74167
       have r₂ := eq36530
       grind)
    | exact resolve eq74167 eq36530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36530 eq74167
  have eq74220 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74171 eq896
    | exact resolve eq896 eq74171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74374 : (τ (σ x)) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74173 eq140
    | exact resolve eq140 eq74173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq74173
  have eq74414 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq74374
    | exact resolve eq74374 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq74374
  have eq74417 : x = (k (M.op x y) x) := by
    first
    | (have r₁ := eq74414
       have r₂ := eq912
       grind)
    | exact resolve eq74414 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912 eq74414
  have eq74437 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74417 eq37148
    | exact resolve eq37148 eq74417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37148 eq74417
  have eq74467 : x = (k y x) := by
    first
    | (have r₁ := eq74437
       have r₂ := eq50
       grind)
    | exact resolve eq74437 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq74437
  have eq74590 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq841 y x
       have i₂ := eq74467
       grind)
    | exact superpose eq74467 eq841
    | (have j0 := eq841 y x
       grind)
    | exact resolve eq841 eq74467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq74467
  have eq74593 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq74590
  have eq74602 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74593
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq74593
    | exact resolve eq74593 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74593
  have eq74626 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74602
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq74602
    | exact resolve eq74602 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74602
  have eq74639 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq74626
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq74626
    | exact resolve eq74626 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74626
  have eq74652 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq74639
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq74639
    | exact resolve eq74639 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74639
  have eq74665 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq74652
    | exact resolve eq74652 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74652
  have eq75056 : (σ x) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74220 eq240
    | exact resolve eq240 eq74220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq74220
  have eq75191 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq896 eq75056
    | exact resolve eq75056 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75056
  have eq75210 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq75191
       have r₂ := eq74171
       grind)
    | exact resolve eq75191 eq74171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75191
  have eq75217 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq896 eq75210
    | exact resolve eq75210 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq75210
  have eq77148 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75217 eq12979
    | (have j0 := eq12979 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq12979 eq75217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12979 eq75217
  have eq77166 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq77148
  have eq77177 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq77166
       have r₂ := eq74171
       grind)
    | exact resolve eq77166 eq74171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77166
  have eq78253 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq77177 eq892
    | exact resolve eq892 eq77177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892 eq77177
  have eq79432 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq78253 eq222
    | exact resolve eq222 eq78253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq78253
  have eq80167 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74171 eq79432
    | exact resolve eq79432 eq74171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74171 eq79432
  have eq80246 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq80167
  have eq80256 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq80246
    | exact resolve eq80246 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq80246
  have eq80723 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80256 eq27
    | exact resolve eq27 eq80256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80256
  have eq80830 : x = (M.op x y) := by
    first
    | (have r₁ := eq80723
       have r₂ := eq36036
       grind)
    | exact resolve eq80723 eq36036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36036 eq80723
  have eq80834 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq80830 eq20
    | exact resolve eq20 eq80830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq80936 : x = (M.op x x) := by
    first
    | exact superpose eq80830 eq894
    | exact resolve eq894 eq80830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq81039 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq80834
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq80834
    | exact resolve eq80834 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80834
  have eq81426 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq80936
       grind)
    | exact superpose eq80936 eq56
    | exact resolve eq56 eq80936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq81584 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq80830 eq81426
    | exact resolve eq81426 eq80830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81426
  have eq81619 : y = (M.op x y) := by
    first
    | (have i₁ := eq81584
       have i₂ := eq80936
       grind)
    | exact superpose eq80936 eq81584
    | exact resolve eq81584 eq80936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80936 eq81584
  have eq81637 : y = (M.op x y) := by
    first
    | (have i₁ := eq81619
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq81619
    | exact resolve eq81619 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq81619
  have eq81648 : x = y := by
    first
    | exact superpose eq80830 eq81637
    | exact resolve eq81637 eq80830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80830 eq81637
  have eq81658 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq81648
       grind)
    | exact superpose eq81648 eq24
    | exact resolve eq24 eq81648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq81648
  have eq81962 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq81658
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq81658
    | exact resolve eq81658 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq81658
  have eq82044 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq81039 eq81962
    | exact resolve eq81962 eq81039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81962
  have eq82324 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq82044 eq74665
    | exact resolve eq74665 eq82044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74665 eq82044
  have eq82330 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq82324
       have r₂ := eq81039
       grind)
    | exact resolve eq82324 eq81039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82324
  have eq82412 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq81039 eq82330
    | exact resolve eq82330 eq81039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81039 eq82330
  have eq82482 : False := by grind
  exact eq82482

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxx_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq192 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
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
  have eq514 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq525 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq517 X0
       grind)
    | exact superpose eq517 eq14
    | exact resolve eq14 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq525
    | exact resolve eq525 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq525
    | exact resolve eq525 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq4154 : ∀ X0 X1 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (M.op (M.op (M.op x (M.op x y)) X0) (M.op (M.op x y) X1)) (M.op (M.op x (M.op x y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq514 sF0 (M.op (M.op x sF0) x) x
       have i₂ := eq14 sF0 (M.op x sF0) x
       grind)
    | exact superpose eq14 eq514
    | exact resolve eq514 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq4168 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X1)) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq875 eq4154
    | exact resolve eq4154 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875 eq4154
  have eq6289 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq192 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq192
    | (have j0 := eq192 y
       grind)
    | exact resolve eq192 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq6310 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6289
  have eq6313 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6310
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq6310
    | exact resolve eq6310 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6310
  have eq6336 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6313
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6313 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6313
  have eq6357 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6336 eq87
    | exact resolve eq87 eq6336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq10244 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6336 eq109
    | exact resolve eq109 eq6336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq17145 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq10244
       grind)
    | exact superpose eq10244 eq16
    | exact resolve eq16 eq10244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10244
  have eq17190 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6357 eq17145
    | exact resolve eq17145 eq6357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17145
  have eq17194 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq17190
       have r₂ := eq13 y y
       grind)
    | exact resolve eq17190 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17190
  have eq17195 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq17194
       grind)
    | exact superpose eq17194 eq76
    | exact resolve eq76 eq17194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq17220 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq6336 eq17195
    | exact resolve eq17195 eq6336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6336 eq17195
  have eq36492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq36502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq36492
    | exact resolve eq36492 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36492
  have eq36513 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq36502
       have r₂ := eq28
       grind)
    | exact resolve eq36502 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36502
  have eq36564 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq36513 eq873
    | exact resolve eq873 eq36513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36513
  have eq36600 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq36564 eq6357
    | exact resolve eq6357 eq36564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36564
  have eq36703 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq36600
       have i₂ := eq17194
       grind)
    | exact superpose eq17194 eq36600
    | exact resolve eq36600 eq17194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36600
  have eq36719 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq36703
    | exact resolve eq36703 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq36703
  have eq37255 : (τ (σ x)) = (k y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq36719 eq6357
    | exact resolve eq6357 eq36719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6357 eq36719
  have eq37335 : (τ (σ x)) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq37255
       have i₂ := eq17194
       grind)
    | exact superpose eq17194 eq37255
    | exact resolve eq37255 eq17194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17194 eq37255
  have eq37344 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq37335
    | exact resolve eq37335 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq37335
  have eq37345 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq37344
  have eq37845 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq525 y X0
       have i₂ := eq37345
       grind)
    | exact superpose eq37345 eq525
    | exact resolve eq525 eq37345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37848 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq37345
       grind)
    | exact superpose eq37345 eq14
    | exact resolve eq14 eq37345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37345
  have eq37921 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq37848 X0
       have i₂ := eq873 y X0
       grind)
    | exact superpose eq873 eq37848
    | exact resolve eq37848 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37848
  have eq38233 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq37845 X0
       have i₂ := eq37921 X0
       grind)
    | exact superpose eq37921 eq37845
    | exact resolve eq37845 eq37921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37845 eq37921
  have eq38312 : ∀ X0 : G, y = (M.op y x) ∨ x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq38233 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38233
  have eq38483 : ∀ X0 : G, y = (M.op y y) ∨ x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq873 y x
       have i₂ := eq38312 X0
       grind)
    | exact superpose eq38312 eq873
    | (have j1 := eq38312 y
       grind)
    | exact resolve eq873 eq38312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38312
  have eq38700 : y ≠ y ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have j0 := eq38483 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38483
  have eq38701 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq38700
  have eq38826 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq525 y X0
       have i₂ := eq38701
       grind)
    | exact superpose eq38701 eq525
    | exact resolve eq525 eq38701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38829 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq38701
       grind)
    | exact superpose eq38701 eq14
    | exact resolve eq14 eq38701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38701
  have eq38902 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq38829 X0
       have i₂ := eq873 y X0
       grind)
    | exact superpose eq873 eq38829
    | exact resolve eq38829 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38829
  have eq39406 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq38826 X0
       have i₂ := eq38902 X0
       grind)
    | exact superpose eq38902 eq38826
    | exact resolve eq38826 eq38902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38826
  have eq39492 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq39406 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39406
  have eq39656 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17220
       have i₂ := eq39492 X0
       grind)
    | exact superpose eq39492 eq17220
    | (have j1 := eq39492 X0
       grind)
    | exact resolve eq17220 eq39492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39715 : ∀ X0 : G, x = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq873 y y
       have i₂ := eq39492 X0
       grind)
    | exact superpose eq39492 eq873
    | (have j1 := eq39492 x
       grind)
    | exact resolve eq873 eq39492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq39492
  have eq39725 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39656 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39656
    | (have j0 := eq39656 X0
       grind)
    | exact resolve eq39656 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq39656
  have eq40342 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq39715 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39715
  have eq40343 : x = (M.op y x) := by grind
  clear eq40342
  have eq40411 : y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq38902 x
       have i₂ := eq40343
       grind)
    | exact superpose eq40343 eq38902
    | exact resolve eq38902 eq40343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38902 eq40343
  have eq40466 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40411
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq40411
    | exact resolve eq40411 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40411
  have eq40488 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq517 y
       have i₂ := eq40466
       grind)
    | exact superpose eq40466 eq517
    | exact resolve eq517 eq40466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40466
  have eq40555 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40488
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq40488
    | exact resolve eq40488 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq40488
  have eq40556 : y = (M.op x y) := by grind
  clear eq40555
  have eq40574 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq40556 eq21
    | exact resolve eq21 eq40556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq40770 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40574
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40574
    | exact resolve eq40574 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40574
  have eq40948 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq40770 eq27
    | exact resolve eq27 eq40770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq43433 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq40770 eq39725
    | (have j0 := eq39725 X0
       grind)
    | exact resolve eq39725 eq40770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39725
  have eq43445 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq517 X0
       have i₂ := eq43433 (M.op X0 X0)
       grind)
    | exact superpose eq43433 eq517
    | (have j1 := eq43433 X0
       grind)
    | exact resolve eq517 eq43433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq43433
  have eq43507 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq40948 eq43445
    | (have j0 := eq43445 X0
       grind)
    | exact resolve eq43445 eq40948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43445
  have eq43518 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq43507 X0
       grind)
    | (have r₁ := eq43507 X0
       have r₂ := eq28
       grind)
    | exact resolve eq43507 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43507
  have eq43569 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq17220
       have i₂ := eq43518 y
       grind)
    | exact superpose eq43518 eq17220
    | exact resolve eq17220 eq43518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17220
  have eq43775 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq40770 eq43569
    | exact resolve eq43569 eq40770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43569
  have eq43835 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq43775
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq43775
    | exact resolve eq43775 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq43775
  have eq43872 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq40770 eq43835
    | exact resolve eq43835 eq40770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40770 eq43835
  have eq44694 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq43872 eq525
    | exact resolve eq525 eq43872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq43872
  have eq44824 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op (M.op y X0) (M.op y X1)) (M.op y X0)) := by
    intro X0 X1
    first
    | exact superpose eq40556 eq4168
    | exact resolve eq4168 eq40556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4168 eq40556
  have eq44825 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44824 X0 X1
       have i₂ := eq43518 X0
       grind)
    | exact superpose eq43518 eq44824
    | exact resolve eq44824 eq43518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44824
  have eq44826 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44825 X0 X1
       have i₂ := eq43518 X1
       grind)
    | exact superpose eq43518 eq44825
    | exact resolve eq44825 eq43518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43518 eq44825
  have eq46982 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44694 x
       have i₂ := eq44826 sF1 x
       grind)
    | exact superpose eq44826 eq44694
    | exact resolve eq44694 eq44826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44694
  have eq47058 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq46982 eq44826
    | exact resolve eq44826 eq46982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44826 eq46982
  have eq47563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47058 eq40948
    | exact resolve eq40948 eq47058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40948 eq47058
  have eq47608 : False := by grind
  exact eq47608

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  clear eq44
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq93 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op (M.op X1 X1) X0) X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq93 x y
       grind)
    | exact superpose eq93 eq45
    | (have j1 := eq93 x y
       grind)
    | exact resolve eq45 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq116
    | exact resolve eq116 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq208 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq491 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq491 (M.op X0 X1)
       grind)
    | exact superpose eq491 eq53
    | exact resolve eq53 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq117 eq93
    | (have j0 := eq93 (σ x) (σ y)
       grind)
    | exact resolve eq93 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq720
    | exact resolve eq720 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq724 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq721
       have r₂ := eq28
       grind)
    | exact resolve eq721 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq734 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq724 eq491
    | exact resolve eq491 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by grind
  have eq736 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq734
    | exact resolve eq734 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq744 : y = (M.op (M.op y x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq495 y y
       have i₂ := eq736
       grind)
    | exact superpose eq736 eq495
    | exact resolve eq495 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq746 : y = (k x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq919 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq746
       grind)
    | exact superpose eq746 eq45
    | exact resolve eq45 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq921 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq919
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq919
    | exact resolve eq919 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq940 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq921 eq93
    | (have j0 := eq93 (σ x) (σ y)
       grind)
    | exact resolve eq93 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq941 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq940
    | exact resolve eq940 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq942 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq941
  have eq956 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq942 eq491
    | exact resolve eq491 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq958 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq956
    | exact resolve eq956 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq959 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq958
  have eq973 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq744
       have i₂ := eq959
       grind)
    | exact superpose eq959 eq744
    | exact resolve eq744 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq976 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq959
       grind)
    | exact superpose eq959 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq959
       grind)
    | exact resolve eq13 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq986 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq976
  have eq989 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq973
  have eq991 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq986
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq986
    | exact resolve eq986 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq994 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq736
       have i₂ := eq989
       grind)
    | exact superpose eq989 eq736
    | exact resolve eq736 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq989
  have eq1012 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq994
  have eq1015 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq1012 eq28
    | exact resolve eq28 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1064 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq991
       grind)
    | exact superpose eq991 eq45
    | exact resolve eq45 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq991
  have eq1068 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1064
    | exact resolve eq1064 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1104 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1068 eq93
    | (have j0 := eq93 (σ x) (σ y)
       grind)
    | exact resolve eq93 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq1104
    | exact resolve eq1104 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1110 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1107
       have r₂ := eq28
       grind)
    | exact resolve eq1107 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1128 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1110 eq491
    | exact resolve eq491 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1130 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq1128
    | exact resolve eq1128 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1131 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1130
  have eq1132 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1131 eq28
    | exact resolve eq28 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1137 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ y) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1131 eq208
    | exact resolve eq208 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq1246 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq1137
    | (have j0 := eq1137 (σ y) X0
       grind)
    | exact resolve eq1137 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq1260 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1131 eq1246
    | exact resolve eq1246 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1265 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1260 (M.op sF3 x)
       have i₂ := eq14 sF3 sF3 x
       grind)
    | exact superpose eq14 eq1260
    | exact resolve eq1260 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq1318 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq724 eq1265
    | exact resolve eq1265 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq1265
  have eq1851 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq735 eq117
    | exact resolve eq117 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq735
  have eq1854 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1851
  have eq1857 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1854
       have r₂ := eq1132
       grind)
    | exact resolve eq1854 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1854
  have eq1860 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1857 eq1318
    | exact resolve eq1318 eq1857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318 eq1857
  have eq1881 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq1860
  have eq1959 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq491 y
       have i₂ := eq1881
       grind)
    | exact superpose eq1881 eq491
    | exact resolve eq491 eq1881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq1881
  have eq1961 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1959
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1959
    | exact resolve eq1959 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq1963 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1961 eq30
    | exact resolve eq30 eq1961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1961
  have eq2037 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1963
    | exact resolve eq1963 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1963
  have eq2095 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2037 eq21
    | exact resolve eq21 eq2037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2037
  have eq2131 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2095
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2095
    | exact resolve eq2095 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2095
  have eq2132 : x = y := by
    first
    | (have r₁ := eq2131
       have r₂ := eq1015
       grind)
    | exact resolve eq2131 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq2131
  have eq2133 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2132
       grind)
    | exact superpose eq2132 eq19
    | exact resolve eq19 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2134 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2132
       grind)
    | exact superpose eq2132 eq25
    | exact resolve eq25 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2132
  have eq2178 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2134
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2134
    | exact resolve eq2134 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2134
  have eq2179 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2178 eq27
    | exact resolve eq27 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2211 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq2178 eq1132
    | exact resolve eq1132 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq2263 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1131 eq2179
    | exact resolve eq2179 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq2179
  have eq2271 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2178 eq2263
    | exact resolve eq2263 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178 eq2263
  have eq2310 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2271 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq2271
       grind)
    | exact resolve eq13 eq2271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271
  have eq2322 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq2310
  have eq2380 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq2322 eq50
    | exact resolve eq50 eq2322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2322
  have eq2384 : x = (k x x) := by
    first
    | exact superpose eq29 eq2380
    | exact resolve eq2380 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2380
  have eq2390 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq93 x x
       have i₂ := eq2384
       grind)
    | exact superpose eq2384 eq93
    | (have j0 := eq93 x x
       grind)
    | exact resolve eq93 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq2384
  have eq2391 : x = (M.op x x) := by grind
  clear eq2390
  have eq2393 : x = (M.op x y) := by
    first
    | (have i₁ := eq2391
       have i₂ := eq2133
       grind)
    | exact superpose eq2133 eq2391
    | exact resolve eq2391 eq2133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133 eq2391
  have eq2397 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2393 eq21
    | exact resolve eq21 eq2393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2393
  have eq2445 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2397
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2397
    | exact resolve eq2397 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2397
  have eq2452 : False := by grind
  exact eq2452

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyx_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (k X0 X0) X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq12 eq13
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
  clear eq37
  have eq85 : ∀ X0 X1 : G, (σ (k (k X0 (M.op x y)) X1)) = (k (k (σ X0) (σ (M.op x y))) (σ X1)) := by
    intro X0 X1
    first
    | exact superpose eq42 eq10
    | exact resolve eq10 eq42
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
  clear eq48
  have eq175 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 y
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq189 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq184 eq16
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq196 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq191 eq16
    | exact resolve eq16 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) (M.op x y)) X1)) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq557 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq184 eq189
    | exact resolve eq189 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq189
  have eq562 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq557
       grind)
    | exact superpose eq557 eq16
    | exact resolve eq16 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq570 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq191 eq196
    | exact resolve eq196 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq196
  have eq575 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq570 eq16
    | exact resolve eq16 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq584 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq562 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq562
    | exact resolve eq562 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq598 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq28 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq668 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq736 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq575 (M.op sF3 x)
       have i₂ := eq16 sF3 sF3 x
       grind)
    | exact superpose eq16 eq575
    | exact resolve eq575 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq892 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq178 eq200
    | exact resolve eq200 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq912 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq892 X0
       grind)
    | exact superpose eq892 eq16
    | exact resolve eq16 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq990 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq892 (M.op X0 X1)
       grind)
    | exact superpose eq892 eq177
    | exact resolve eq177 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1076 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq180 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq892 (M.op X0 X1)
       grind)
    | exact superpose eq892 eq180
    | exact resolve eq180 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1178 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq990 X0 X0
       have i₂ := eq598 X0
       grind)
    | exact superpose eq598 eq990
    | exact resolve eq990 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1198 : ∀ X0 : G, (M.op (k (k X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1178 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq1178
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq1178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1211 : ∀ X0 : G, (M.op (k (k X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1198 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1224 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq912 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq912
    | exact resolve eq912 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1228 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq178 eq912
    | exact resolve eq912 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq912
  have eq1252 : x ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq1228 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1253 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op x X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1228 eq16
    | exact resolve eq16 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1323 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq598 X0
       have i₂ := eq1224 X0 X0
       grind)
    | exact superpose eq1224 eq598
    | exact resolve eq598 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq1326 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq1224 X0 X1
       grind)
    | exact superpose eq1224 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1361 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X1 X0) = (k (k X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq13 eq1326
    | (have j0 := eq1326 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | exact resolve eq1326 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1409 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1323 x
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq1323
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq1323 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1417 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq42 (M.op sF0 sF0)
       have i₂ := eq1323 sF0
       grind)
    | exact superpose eq1323 eq42
    | exact resolve eq42 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1421 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1409 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1422 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq1421 X0
       have j1 := eq1361 X0 X0
       grind)
    | (have r₁ := eq1421 x
       have r₂ := eq1361 x x
       grind)
    | exact resolve eq1421 eq1361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361 eq1421
  have eq1666 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq644
       grind)
    | exact superpose eq644 eq41
    | exact resolve eq41 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq1667 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1666
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1666
    | exact resolve eq1666 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666
  have eq1669 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq1667
    | exact resolve eq1667 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667
  have eq17029 : ∀ X0 : G, (k (k (k X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 (k (k X0 X0) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k (k X0 X0) X0) X0
       have i₂ := eq1211 X0
       grind)
    | exact superpose eq1211 eq11
    | (have j0 := eq11 (k (k X0 X0) X0) X0
       have j1 := eq1211 X0
       grind)
    | exact resolve eq11 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq17067 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 (k (k X0 X0) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17029 X0
       have i₂ := eq1422 X0
       grind)
    | exact superpose eq1422 eq17029
    | (have j0 := eq17029 X0
       grind)
    | exact resolve eq17029 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17029
  have eq17080 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 (k (k X0 X0) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17067 X0
       have i₂ := eq1422 X0
       grind)
    | exact superpose eq1422 eq17067
    | (have j0 := eq17067 X0
       grind)
    | exact resolve eq17067 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17067
  have eq17091 : ∀ X0 : G, (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 (k (k X0 X0) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq17080 X0
       have j1 := eq669 X0
       grind)
    | (have r₁ := eq17080 X0
       have r₂ := eq669 X0
       grind)
    | exact resolve eq17080 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq17080
  have eq17094 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 (k (k X0 X0) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17091 X0
       have i₂ := eq1422 X0
       grind)
    | exact superpose eq1422 eq17091
    | (have j0 := eq17091 X0
       grind)
    | exact resolve eq17091 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17091
  have eq17096 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 (k (k X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq17094 X0
       have j1 := eq28 X0 X0
       grind)
    | (have r₁ := eq17094 x
       have r₂ := eq28 (k x x) x
       grind)
    | (have r₁ := eq17094 (M.op x x)
       have r₂ := eq28 (M.op (M.op x x) (k (k (M.op x x) (M.op x x)) (M.op x x))) x
       grind)
    | (have r₁ := eq17094 X0
       have r₂ := eq28 X0 X0
       grind)
    | exact resolve eq17094 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq17094
  have eq17098 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq17096 X0
       have i₂ := eq1422 X0
       grind)
    | exact superpose eq1422 eq17096
    | (have j0 := eq17096 X0
       grind)
    | exact resolve eq17096 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422 eq17096
  have eq17357 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1224 X0 (k X0 X0)
       have i₂ := eq17098 X0
       grind)
    | exact superpose eq17098 eq1224
    | (have j1 := eq17098 X0
       grind)
    | exact resolve eq1224 eq17098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17407 : y = (M.op y y) ∨ (k y y) = (M.op y y) := by
    first
    | (have i₁ := eq584 (k y y)
       have i₂ := eq17098 y
       grind)
    | exact superpose eq17098 eq584
    | (have j1 := eq17098 y
       grind)
    | exact resolve eq584 eq17098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17419 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq736 (k sF3 sF3)
       have i₂ := eq17098 sF3
       grind)
    | exact superpose eq17098 eq736
    | (have j1 := eq17098 (σ y)
       grind)
    | exact resolve eq736 eq17098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq17098
  have eq17424 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq17419
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq17419 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17419
  have eq17430 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq17407
       have r₂ := eq13 y y
       grind)
    | exact resolve eq17407 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17407
  have eq17464 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq17357 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq17357 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq17357 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17357
  have eq17598 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq892 X0
       have i₂ := eq17464 X0
       grind)
    | exact superpose eq17464 eq892
    | exact resolve eq892 eq17464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq17606 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq17464 X0
       grind)
    | exact superpose eq17464 eq16
    | exact resolve eq16 eq17464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17607 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq17464 X0
       grind)
    | exact superpose eq17464 eq16
    | exact resolve eq16 eq17464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17831 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq17598 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq17598
    | exact resolve eq17598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1669 eq658
    | exact resolve eq658 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq23526 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq23513
       have r₂ := eq27
       grind)
    | exact resolve eq23513 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23513
  have eq23535 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17424 eq23526
    | exact resolve eq23526 eq17424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23526
  have eq23539 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq23535
       have i₂ := eq17430
       grind)
    | exact superpose eq17430 eq23535
    | exact resolve eq23535 eq17430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23535
  have eq23547 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq23539 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq23539
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq23539
       grind)
    | exact resolve eq13 eq23539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23567 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq23539 eq1224
    | exact resolve eq1224 eq23539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23539
  have eq23573 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by grind
  clear eq23547
  have eq23577 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17424 eq23567
    | exact resolve eq23567 eq17424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17424 eq23567
  have eq23613 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq23573 eq1669
    | exact resolve eq1669 eq23573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669 eq23573
  have eq23623 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by grind
  clear eq23613
  have eq23630 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq23623
       have i₂ := eq17430
       grind)
    | exact superpose eq17430 eq23623
    | exact resolve eq23623 eq17430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17430 eq23623
  have eq23631 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (k y y) := by grind
  clear eq23630
  have eq23637 : (τ (σ x)) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (k y y) := by
    first
    | exact superpose eq23631 eq116
    | exact resolve eq116 eq23631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23631
  have eq23697 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq23637
    | exact resolve eq23637 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23637
  have eq23698 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by grind
  clear eq23697
  have eq23715 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq23698
       grind)
    | exact superpose eq23698 eq16
    | exact resolve eq16 eq23698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23759 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq23715 X0
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq23715
    | exact resolve eq23715 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq23715
  have eq24376 : (M.op y x) = (M.op x (M.op y x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1076 y x
       have i₂ := eq23759 x
       grind)
    | exact superpose eq23759 eq1076
    | exact resolve eq1076 eq23759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076 eq23759
  have eq24417 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | exact superpose eq23698 eq24376
    | exact resolve eq24376 eq23698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23698 eq24376
  have eq24426 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24417
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24417
    | exact resolve eq24417 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24417
  have eq24453 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17598 y
       have i₂ := eq24426
       grind)
    | exact superpose eq24426 eq17598
    | exact resolve eq17598 eq24426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17598 eq24426
  have eq24475 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24453
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24453
    | exact resolve eq24453 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq24453
  have eq24476 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq24475
  have eq24494 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24476 eq29
    | exact resolve eq29 eq24476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq24476
  have eq24589 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq24494
    | exact resolve eq24494 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24494
  have eq24590 : y = (M.op x y) := by grind
  clear eq24589
  have eq24604 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq24590
       grind)
    | exact superpose eq24590 eq24
    | exact resolve eq24 eq24590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq24606 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq24590
       grind)
    | exact superpose eq24590 eq41
    | exact resolve eq41 eq24590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq24694 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24604 eq20
    | exact resolve eq20 eq24604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24764 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq24604 eq329
    | exact resolve eq329 eq24604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq25573 : ∀ X0 X1 : G, (k (k (σ X1) (σ (M.op x y))) (k (σ X0) (σ y))) = (σ (k (k X1 (M.op x y)) (k X0 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq24606 eq85
    | exact resolve eq85 eq24606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq24606
  have eq25666 : ∀ X0 X1 : G, (k (k (σ X1) (σ y)) (k (σ X0) (σ y))) = (σ (k (k X1 (M.op x y)) (k X0 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq24694 eq25573
    | exact resolve eq25573 eq24694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25573
  have eq65604 : ∀ X0 X1 : G, (M.op (M.op (M.op (k (σ X0) (σ y)) X1) (σ (k (k X0 (M.op x y)) (k X0 (M.op x y))))) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq25666 eq17607
    | exact resolve eq17607 eq25666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25666
  have eq156697 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq23577 eq24764
    | exact resolve eq24764 eq23577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23577 eq24764
  have eq156753 : y = (k y (M.op x y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq156697
    | exact resolve eq156697 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq156697
  have eq156794 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq156753
       have i₂ := eq24590
       grind)
    | exact superpose eq24590 eq156753
    | exact resolve eq156753 eq24590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156753
  have eq156829 : x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq156794
       have i₂ := eq24590
       grind)
    | exact superpose eq24590 eq156794
    | exact resolve eq156794 eq24590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156794
  have eq156861 : (σ x) = (k (σ y) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq156829
       have i₂ := eq24590
       grind)
    | exact superpose eq24590 eq156829
    | exact resolve eq156829 eq24590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156829
  have eq158581 : (τ (σ x)) = (k y y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq156861 eq116
    | exact resolve eq116 eq156861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq156861
  have eq158684 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq158581
       have i₂ := eq24590
       grind)
    | exact superpose eq24590 eq158581
    | exact resolve eq158581 eq24590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24590 eq158581
  have eq158705 : x = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq30 eq158684
    | exact resolve eq158684 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq158684
  have eq158706 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq158705
  have eq158786 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq158706 eq17606
    | exact resolve eq17606 eq158706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17606
  have eq158787 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X0) = X0 ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq158706 eq17607
    | exact resolve eq17607 eq158706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17607 eq158706
  have eq158812 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq158786 x
       have i₂ := eq1224 sF0 x
       grind)
    | exact superpose eq1224 eq158786
    | exact resolve eq158786 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224 eq158786
  have eq159787 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq158812 eq158787
    | exact resolve eq158787 eq158812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158787 eq158812
  have eq159863 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq159787 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159787
  have eq160048 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq990 X0 x
       have i₂ := eq159863 (M.op X0 x)
       grind)
    | exact superpose eq159863 eq990
    | (have j1 := eq159863 X0
       grind)
    | exact resolve eq990 eq159863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq160083 : ∀ X0 : G, x = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1228 eq160048
    | (have j0 := eq160048 x
       grind)
    | exact resolve eq160048 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228 eq160048
  have eq160107 : ∀ X0 : G, x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq159863 eq160083
    | (have j0 := eq160083 X0
       have j1 := eq159863 X0
       grind)
    | exact resolve eq160083 eq159863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159863 eq160083
  have eq160208 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17831 X0
       have i₂ := eq160107 (k X0 X0)
       grind)
    | exact superpose eq160107 eq17831
    | (have j1 := eq160107 X0
       grind)
    | exact resolve eq17831 eq160107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17831 eq160107
  have eq160222 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq160208
    | (have j0 := eq160208 X0
       grind)
    | exact resolve eq160208 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160208
  have eq160258 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq24694 eq160222
    | (have j0 := eq160222 X0
       grind)
    | exact resolve eq160222 eq24694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160222
  have eq160279 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq160258 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq160258
    | (have j0 := eq160258 X0
       grind)
    | exact resolve eq160258 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160258
  have eq160294 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq160279
    | (have j0 := eq160279 X0
       grind)
    | exact resolve eq160279 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160279
  have eq160350 : ∀ X0 : G, (M.op x y) = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq160294 eq1253
    | exact resolve eq1253 eq160294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq160377 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq160294 eq1417
    | exact resolve eq1417 eq160294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq160397 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq160294 eq17464
    | exact resolve eq17464 eq160294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160401 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X1) X0) X1) = X1 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq160294 eq16
    | exact resolve eq16 eq160294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160518 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq160294 eq160401
    | exact resolve eq160401 eq160294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160401
  have eq160527 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24694 eq160377
    | exact resolve eq160377 eq24694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160377
  have eq160567 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq160527
    | exact resolve eq160527 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160527
  have eq160581 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24694 eq160567
    | exact resolve eq160567 eq24694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160567
  have eq160636 : ∀ X0 : G, (M.op (M.op (M.op (k (σ (M.op x y)) (σ y)) X0) (σ (k (M.op x y) (M.op x y)))) X0) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq160397 eq65604
    | exact resolve eq65604 eq160397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65604 eq160397
  have eq160687 : ∀ X0 : G, (M.op (M.op (M.op (k (σ (M.op x y)) (σ y)) X0) (k (σ (M.op x y)) (σ (M.op x y)))) X0) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq42 eq160636
    | exact resolve eq160636 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq160636
  have eq160717 : ∀ X0 : G, (M.op (M.op (M.op (k (σ (M.op x y)) (σ y)) X0) (k (σ (M.op x y)) (σ y))) X0) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24694 eq160687
    | exact resolve eq160687 eq24694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160687
  have eq160744 : ∀ X0 : G, (M.op (M.op (M.op (k (σ (M.op x y)) (σ y)) X0) (k (σ (M.op x y)) (σ y))) X0) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq160717
    | (have j0 := eq160717 X0
       grind)
    | exact resolve eq160717 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160717
  have eq160757 : ∀ X0 : G, (M.op (M.op (M.op (k (σ y) (σ y)) X0) (k (σ y) (σ y))) X0) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24694 eq160744
    | exact resolve eq160744 eq24694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160744
  have eq160768 : ∀ X0 : G, (M.op (k (σ y) (σ y)) X0) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq160518 eq160757
    | exact resolve eq160757 eq160518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160518 eq160757
  have eq160777 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq160581 eq160768
    | exact resolve eq160768 eq160581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160581 eq160768
  have eq161083 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (M.op x (σ y)) (M.op x y)) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq160777 eq201
    | exact resolve eq201 eq160777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq160777
  have eq161123 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op x y) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq160350 eq161083
    | exact resolve eq161083 eq160350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160350 eq161083
  have eq161164 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq160294 eq161123
    | exact resolve eq161123 eq160294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160294 eq161123
  have eq161551 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq161164 eq26
    | (have j1 := eq161164 (σ x)
       grind)
    | exact resolve eq26 eq161164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161164
  have eq161592 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq161551
  have eq161601 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq161592 eq27
    | exact resolve eq27 eq161592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161592
  have eq161674 : x = (M.op x y) := by
    first
    | (have r₁ := eq161601
       have r₂ := eq24694
       grind)
    | exact resolve eq161601 eq24694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161601
  have eq161679 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq161674
       grind)
    | exact superpose eq161674 eq22
    | exact resolve eq22 eq161674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq161716 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1252
       have i₂ := eq161674
       grind)
    | exact superpose eq161674 eq1252
    | (have r₁ := eq1252
       have r₂ := eq161674
       grind)
    | exact resolve eq1252 eq161674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252 eq161674
  have eq161893 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq161716
  have eq162038 : (σ x) = (σ y) := by
    first
    | exact superpose eq161679 eq24604
    | exact resolve eq24604 eq161679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24604
  have eq162039 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq161679 eq20
    | exact resolve eq20 eq161679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161679
  have eq163117 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq162038 eq26
    | exact resolve eq26 eq162038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq163499 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq163117
       have i₂ := eq17464 sF2
       grind)
    | exact superpose eq17464 eq163117
    | exact resolve eq163117 eq17464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17464 eq163117
  have eq164740 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq161893 eq38
    | exact resolve eq38 eq161893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq161893
  have eq164795 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq164740
    | exact resolve eq164740 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq164740
  have eq164830 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq24694 eq164795
    | exact resolve eq164795 eq24694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24694 eq164795
  have eq164860 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq162038 eq164830
    | exact resolve eq164830 eq162038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162038 eq164830
  have eq165217 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq163499 eq164860
    | exact resolve eq164860 eq163499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163499 eq164860
  have eq165315 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq165217 eq27
    | exact resolve eq27 eq165217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq165217
  have eq165422 : False := by grind
  exact eq165422
