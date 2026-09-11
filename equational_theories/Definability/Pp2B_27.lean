import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq78 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
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
  have eq788 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq77 X0 X1
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
  have eq798 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq800 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq798 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq802 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq788 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq804 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq802 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq802 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq802 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq802 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq814 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq804 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq804
    | (have j0 := eq804 X0 X1
       grind)
    | exact resolve eq804 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq848 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
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
  have eq850 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq53 eq533
    | exact resolve eq533 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq852 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54 eq533
    | exact resolve eq533 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq533
  have eq866 : x ≠ (M.op x y) ∨ (M.op (M.op x y) x) = (k (M.op x y) x) := by
    first
    | exact superpose eq850 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3968 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq800 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq800
    | (have j0 := eq800 (τ X0)
       grind)
    | exact resolve eq800 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq800
  have eq3976 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3968 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3968
    | (have j0 := eq3968 X0
       grind)
    | exact resolve eq3968 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3968
  have eq3982 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3976 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3976
    | (have j0 := eq3976 X0
       grind)
    | exact resolve eq3976 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3976
  have eq6457 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq6484 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6457
  have eq6489 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6484
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq6484
    | exact resolve eq6484 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq6484
  have eq6507 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6489
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6489 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6489
  have eq6511 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6507 eq49
    | exact resolve eq49 eq6507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq6507
  have eq6831 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq137
    | (have j0 := eq137 (M.op x y)
       grind)
    | exact resolve eq137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq6856 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6831
  have eq6859 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq136 eq6856
    | exact resolve eq6856 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq6856
  have eq6891 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6859
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6859 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6859
  have eq6927 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq6891 eq159
    | exact resolve eq159 eq6891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq6891
  have eq9532 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq9533 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq9532
    | exact resolve eq9532 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9532
  have eq9544 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq9533
       have r₂ := eq27
       grind)
    | exact resolve eq9533 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9533
  have eq9546 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq9544
    | exact resolve eq9544 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9544
  have eq9550 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq9546 eq14
    | exact resolve eq14 eq9546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9571 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9546 eq848
    | exact resolve eq848 eq9546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9584 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9550 x
       have i₂ := eq848 sF3 x
       grind)
    | exact superpose eq848 eq9550
    | exact resolve eq9550 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9550
  have eq10865 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9571 eq9584
    | exact resolve eq9584 eq9571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9571
  have eq10920 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq10865
  have eq11160 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq10920 eq9546
    | exact resolve eq9546 eq10920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9546
  have eq11161 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq10920 eq9584
    | exact resolve eq9584 eq10920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9584 eq10920
  have eq11198 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq11161
  have eq11199 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq11160
  have eq11209 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq11199
       grind)
    | exact superpose eq11199 eq14
    | exact resolve eq14 eq11199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11262 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq11209 X0
       have i₂ := eq848 y X0
       grind)
    | exact superpose eq848 eq11209
    | exact resolve eq11209 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq11209
  have eq13884 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11262 x
       have i₂ := eq11199
       grind)
    | exact superpose eq11199 eq11262
    | exact resolve eq11262 eq11199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11262
  have eq13946 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq13884
  have eq14836 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11199
       have i₂ := eq13946
       grind)
    | exact superpose eq13946 eq11199
    | exact resolve eq11199 eq13946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11199 eq13946
  have eq14879 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq14836
  have eq14892 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14879 eq222
    | exact resolve eq222 eq14879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq14915 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14879 eq852
    | exact resolve eq852 eq14879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq22250 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14915 eq14892
    | exact resolve eq14892 eq14915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14892 eq14915
  have eq22293 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq22250
  have eq22300 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq22293
    | exact resolve eq22293 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22293
  have eq22345 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22300 eq14879
    | exact resolve eq14879 eq22300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14879 eq22300
  have eq22358 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq22345
  have eq22764 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq22358 eq29
    | exact resolve eq29 eq22358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq22358
  have eq22930 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq22764
    | exact resolve eq22764 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22764
  have eq22931 : x = (M.op x y) ∨ x = y := by grind
  clear eq22930
  have eq22932 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq22931 eq20
    | exact resolve eq20 eq22931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23012 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq22931 eq850
    | exact resolve eq850 eq22931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq23088 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22932
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22932
    | exact resolve eq22932 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22932
  have eq23734 : x ≠ x ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq23012
       grind)
    | exact superpose eq23012 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq23012
       grind)
    | exact resolve eq13 eq23012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23012
  have eq23771 : x = (k x x) ∨ x = y := by grind
  clear eq23734
  have eq24362 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq814 x x
       have i₂ := eq23771
       grind)
    | exact superpose eq23771 eq814
    | (have j0 := eq814 x x
       grind)
    | exact resolve eq814 eq23771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq23771
  have eq24363 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq24362
  have eq24364 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq24363
  have eq24379 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq24364
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24364
    | exact resolve eq24364 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24364
  have eq25186 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq23088 eq24379
    | exact resolve eq24379 eq23088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23088 eq24379
  have eq25262 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq25186
  have eq25648 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq25262 eq6927
    | exact resolve eq6927 eq25262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6927 eq25262
  have eq25727 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30 eq25648
    | exact resolve eq25648 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq25648
  have eq25799 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq25727 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq25727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25727
  have eq25821 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq25799
  have eq25913 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq25821 eq213
    | exact resolve eq213 eq25821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq25821
  have eq27078 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq22931 eq25913
    | exact resolve eq25913 eq22931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25913
  have eq27124 : y = (M.op x y) ∨ x = y := by grind
  clear eq27078
  have eq27127 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq27124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27124
    | exact resolve eq27124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27124
  have eq27533 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq27127 eq22931
    | exact resolve eq22931 eq27127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22931 eq27127
  have eq27544 : x = y := by grind
  clear eq27533
  have eq27639 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq27544
       grind)
    | exact superpose eq27544 eq18
    | exact resolve eq18 eq27544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq27640 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq27544
       grind)
    | exact superpose eq27544 eq24
    | exact resolve eq24 eq27544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq27784 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27640
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27640
    | exact resolve eq27640 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27640
  have eq28275 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27784 eq26
    | exact resolve eq26 eq27784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq27784
  have eq29184 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq28275 eq6511
    | exact resolve eq6511 eq28275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6511
  have eq29192 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28275 eq11198
    | exact resolve eq11198 eq28275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11198 eq28275
  have eq29275 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq29192
  have eq29289 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29275
       have i₂ := eq27544
       grind)
    | exact superpose eq27544 eq29275
    | exact resolve eq29275 eq27544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27544 eq29275
  have eq29297 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29289
       have i₂ := eq27639
       grind)
    | exact superpose eq27639 eq29289
    | exact resolve eq29289 eq27639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29289
  have eq29298 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq29297
  have eq32317 : x ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3982 x
       have i₂ := eq29184
       grind)
    | exact superpose eq29184 eq3982
    | (have j0 := eq3982 x
       grind)
    | exact resolve eq3982 eq29184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3982
  have eq32355 : x ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32317
       have i₂ := eq27639
       grind)
    | exact superpose eq27639 eq32317
    | exact resolve eq32317 eq27639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32317
  have eq32741 : x ≠ (τ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29298 eq32355
    | exact resolve eq32355 eq29298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29298 eq32355
  have eq32748 : x ≠ (τ (σ x)) ∨ x = (M.op x y) := by grind
  clear eq32741
  have eq32749 : x = (M.op x y) := by
    first
    | (have r₁ := eq32748
       have r₂ := eq28
       grind)
    | exact resolve eq32748 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq32748
  have eq32778 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq32749 eq20
    | exact resolve eq20 eq32749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq32859 : x ≠ x ∨ (k x x) = (M.op x x) := by
    first
    | exact superpose eq32749 eq866
    | (have r₁ := eq866
       have r₂ := eq32749
       grind)
    | exact resolve eq866 eq32749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq32877 : (k x x) = (M.op x x) := by grind
  clear eq32859
  have eq32887 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq32877
       have i₂ := eq27639
       grind)
    | exact superpose eq27639 eq32877
    | exact resolve eq32877 eq27639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27639 eq32877
  have eq32959 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq32778
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32778
    | exact resolve eq32778 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32778
  have eq32964 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32887
       have i₂ := eq29184
       grind)
    | exact superpose eq29184 eq32887
    | exact resolve eq32887 eq29184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29184 eq32887
  have eq33024 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32749 eq32964
    | exact resolve eq32964 eq32749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32749 eq32964
  have eq33424 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33024 eq15
    | exact resolve eq15 eq33024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33024
  have eq33476 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33424
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33424
    | exact resolve eq33424 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq33424
  have eq33492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32959 eq33476
    | exact resolve eq33476 eq32959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32959 eq33476
  have eq33506 : False := by grind
  exact eq33506

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  clear eq18
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq41 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) ≠ X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq31
    | exact resolve eq31 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op X0 X1) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq32
    | exact resolve eq32 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq275 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) ∨ (M.op X0 (τ X1)) = X0 := by
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
  clear eq17
  have eq328 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq269 y x
       grind)
    | exact superpose eq269 eq16
    | (have j1 := eq269 y x
       grind)
    | exact resolve eq16 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X1) X2) (σ (k X0 X1))) X2) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X1) (σ X0)
       have i₂ := eq269 X0 X1
       grind)
    | exact superpose eq269 eq9
    | (have j1 := eq269 X0 X1
       grind)
    | exact resolve eq9 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq269 X0 X1
       grind)
    | exact superpose eq269 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq269 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq269 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq269 X0 X1
       grind)
    | exact resolve eq12 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq353 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq331 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq331 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq331 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq331 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq357 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq353 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq353
    | (have j0 := eq353 X0 X1
       grind)
    | exact resolve eq353 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq515 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X4) X0) ≠ X4 ∨ (k X4 (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X4) X0)) = (M.op X4 (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X4) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq41 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3
       have i₂ := eq32 X0 X1 X2 X3
       grind)
    | exact superpose eq32 eq41
    | exact resolve eq41 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq41
  have eq533 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq620 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2) (M.op (M.op X0 X0) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq229 X0 (M.op (M.op X0 X0) X1) X2
       have i₂ := eq94 (M.op X0 X0) X1
       grind)
    | exact superpose eq94 eq229
    | exact resolve eq229 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq850 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq94 X0 X0
       grind)
    | exact superpose eq94 eq75
    | (have j0 := eq75 X0
       grind)
    | exact resolve eq75 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq5048 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq275 (M.op (τ x) (τ x)) x
       have i₂ := eq68 (τ x)
       grind)
    | exact superpose eq68 eq275
    | (have j0 := eq275 (τ X0) X0
       grind)
    | exact resolve eq275 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5160 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5048 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5048
    | (have j0 := eq5048 X0
       grind)
    | exact resolve eq5048 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5048
  have eq5205 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5160 X0
       have i₂ := eq94 (τ X0) (τ X0)
       grind)
    | exact superpose eq94 eq5160
    | (have j0 := eq5160 X0
       grind)
    | exact resolve eq5160 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5160
  have eq5206 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq5205 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5205
  have eq5216 : ∀ X0 : G, (k X0 (k X0 (σ (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5206 X0
       have i₂ := eq275 (τ X0) X0
       grind)
    | exact superpose eq275 eq5206
    | (have j0 := eq5206 X0
       have j1 := eq275 (τ X0) X0
       grind)
    | exact resolve eq5206 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq5228 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq5206 (σ X0)
       grind)
    | exact superpose eq5206 eq28
    | (have j1 := eq5206 (σ X0)
       grind)
    | exact resolve eq28 eq5206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5206
  have eq5234 : ∀ X0 : G, (k X0 (k X0 (σ (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq5216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216
  have eq5240 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5228 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq5228
    | (have j0 := eq5228 X0
       grind)
    | exact resolve eq5228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5228
  have eq5247 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5234 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5234
    | (have j0 := eq5234 X0
       grind)
    | exact resolve eq5234 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5234
  have eq5253 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5240 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5240
    | (have j0 := eq5240 X0
       grind)
    | exact resolve eq5240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5240
  have eq5260 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5253 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5253
    | (have j0 := eq5253 X0
       grind)
    | exact resolve eq5253 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5253
  have eq5346 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) (τ X0)
       have i₂ := eq5247 X0
       grind)
    | exact superpose eq5247 eq12
    | (have j1 := eq5247 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq5247 X0
       grind)
    | exact resolve eq12 eq5247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5371 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq112 (τ X0) (τ X0)
       have i₂ := eq5247 X0
       grind)
    | exact superpose eq5247 eq112
    | (have j1 := eq5247 X0
       grind)
    | (have r₁ := eq112 (τ X0) (τ X0)
       have r₂ := eq5247 X0
       grind)
    | exact resolve eq112 eq5247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq5247
  have eq5400 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq5371 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5371
  have eq5401 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq5346 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5346
  have eq5413 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5400 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq5400
    | (have j0 := eq5400 X0
       grind)
    | exact resolve eq5400 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5400
  have eq5423 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5401 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq5401
    | (have j0 := eq5401 X0
       grind)
    | exact resolve eq5401 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5401
  have eq6197 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq328
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq328
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq328 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq6198 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq6197
  have eq7309 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ (k X0 X0)) = (k (τ X0) (τ (k X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq850 (τ X0)
       have i₂ := eq5413 X0
       grind)
    | exact superpose eq5413 eq850
    | (have j1 := eq5413 X0
       grind)
    | exact resolve eq850 eq5413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5413
  have eq7389 : ∀ X0 : G, (τ (k X0 X0)) = (k (τ X0) (τ (k X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq7309 X0
       have j1 := eq5423 X0
       grind)
    | (have r₁ := eq7309 X0
       have r₂ := eq5423 X0
       grind)
    | exact resolve eq7309 eq5423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5423 eq7309
  have eq7395 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k X0 (k X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq7389 X0
       have i₂ := eq33 (k X0 X0) X0
       grind)
    | exact superpose eq33 eq7389
    | (have j0 := eq7389 X0
       grind)
    | exact resolve eq7389 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7389
  have eq7436 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X1)) X2) (σ (τ (k X0 X1)))) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq330 (τ X0) (τ X1) X2
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq330
    | (have j0 := eq330 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq330 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq330
  have eq7537 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X1)) X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7436 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7436
    | (have j0 := eq7436 X0 X1 X2
       grind)
    | exact resolve eq7436 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7436
  have eq7545 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7537 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7537
    | (have j0 := eq7537 X0 X1 X2
       grind)
    | exact resolve eq7537 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7537
  have eq7551 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7545 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7545
    | (have j0 := eq7545 X0 X1 X2
       grind)
    | exact resolve eq7545 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7545
  have eq7556 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7551 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7551
    | (have j0 := eq7551 X0 X1 X2
       grind)
    | exact resolve eq7551 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7551
  have eq7561 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7556 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7556
    | (have j0 := eq7556 X0 X1 X2
       grind)
    | exact resolve eq7556 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7556
  have eq7566 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7561 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7561
    | (have j0 := eq7561 X0 X1 X2
       grind)
    | exact resolve eq7561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7561
  have eq14574 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = (k (M.op (M.op X0 X0) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq515 x x x x (M.op (M.op x x) (M.op x x))
       have i₂ := eq620 x (M.op x x) x
       grind)
    | exact superpose eq620 eq515
    | exact resolve eq515 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515 eq620
  have eq14577 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) ≠ X0 ∨ (k (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14574 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq14574
    | (have j0 := eq14574 X0 X1
       grind)
    | exact resolve eq14574 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14574
  have eq22637 : ∀ X0 : G, (σ (τ (k X0 X0))) = (k X0 (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 (k X0 X0))
       have i₂ := eq7395 X0
       grind)
    | exact superpose eq7395 eq11
    | (have j1 := eq7395 X0
       grind)
    | exact resolve eq11 eq7395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7395
  have eq22689 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq22637 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq22637
    | (have j0 := eq22637 X0
       grind)
    | exact resolve eq22637 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22637
  have eq22750 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22689 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq22689
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq22689 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22689
  have eq22895 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq22750 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22750
  have eq22934 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq22895 X0
       have j1 := eq850 X0
       grind)
    | (have r₁ := eq22895 X0
       have r₂ := eq850 X0
       grind)
    | exact resolve eq22895 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq22895
  have eq23328 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq22934 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22934
  have eq23345 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq23328 X0
       have j1 := eq5260 X0
       grind)
    | (have r₁ := eq23328 X0
       have r₂ := eq5260 X0
       grind)
    | exact resolve eq23328 eq5260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5260 eq23328
  have eq23400 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq357 X0 (M.op X0 X0)
       have i₂ := eq23345 X0
       grind)
    | exact superpose eq23345 eq357
    | (have j0 := eq357 X0 (M.op X0 X0)
       grind)
    | exact resolve eq357 eq23345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq23345
  have eq23432 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq23400 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23400
  have eq35729 : (σ y) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ y) = (k (M.op (M.op (σ y) (σ y)) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14577 (σ y) (σ x)
       have i₂ := eq6198
       grind)
    | exact superpose eq6198 eq14577
    | exact resolve eq14577 eq6198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6198
  have eq35736 : (σ y) = (k (M.op (M.op (σ y) (σ y)) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq35729
       have r₂ := eq68 (σ y)
       grind)
    | exact resolve eq35729 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35729
  have eq35780 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35736
       have i₂ := eq68 (σ y)
       grind)
    | exact superpose eq68 eq35736
    | exact resolve eq35736 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35736
  have eq35792 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35780
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq35780
    | exact resolve eq35780 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35780
  have eq42673 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 (k X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (k X1 X0)
       have i₂ := eq7566 X1 X0 X0
       grind)
    | exact superpose eq7566 eq76
    | (have j1 := eq7566 X1 X0 x
       grind)
    | exact resolve eq76 eq7566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7566
  have eq490261 : (σ x) ≠ (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (k (M.op (M.op (σ x) (σ x)) (σ x)) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14577 (σ x) (σ y)
       have i₂ := eq35792
       grind)
    | exact superpose eq35792 eq14577
    | exact resolve eq14577 eq35792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14577 eq35792
  have eq490458 : (σ x) = (k (M.op (M.op (σ x) (σ x)) (σ x)) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq490261
       have r₂ := eq68 (σ x)
       grind)
    | exact resolve eq490261 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490261
  have eq490639 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq490458
       have i₂ := eq68 (σ x)
       grind)
    | exact superpose eq68 eq490458
    | exact resolve eq490458 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq490458
  have eq490651 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq490639
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq490639
    | exact resolve eq490639 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490639
  have eq490704 : (τ (σ y)) = (k y y) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq490651
       grind)
    | exact superpose eq490651 eq10
    | exact resolve eq10 eq490651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490651
  have eq490903 : (σ x) = (σ (k x x)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq490704
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq490704
    | exact resolve eq490704 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490704
  have eq490963 : (τ (σ x)) = (k x x) ∨ y = (k y y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq490903
       grind)
    | exact superpose eq490903 eq10
    | exact resolve eq10 eq490903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490903
  have eq491162 : y = (k y y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq490963
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq490963
    | exact resolve eq490963 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490963
  have eq491507 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42673 y y
       have i₂ := eq491162
       grind)
    | exact superpose eq491162 eq42673
    | (have j0 := eq42673 y y
       grind)
    | exact resolve eq42673 eq491162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491162
  have eq491536 : y = (M.op y y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq491507
  have eq491688 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq491536
       grind)
    | exact superpose eq491536 eq76
    | exact resolve eq76 eq491536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491807 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq533 y y x
       have i₂ := eq491536
       grind)
    | exact superpose eq491536 eq533
    | exact resolve eq533 eq491536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491536
  have eq492304 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq491807 X0
       have i₂ := eq94 y X0
       grind)
    | exact superpose eq94 eq491807
    | exact resolve eq491807 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491807
  have eq506311 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq491688 X0
       have i₂ := eq492304 X0
       grind)
    | exact superpose eq492304 eq491688
    | exact resolve eq491688 eq492304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491688 eq492304
  have eq507015 : ∀ X0 : G, y = (M.op y x) ∨ x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq506311 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506311
  have eq507100 : ∀ X0 : G, y = (M.op y y) ∨ x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq94 y x
       have i₂ := eq507015 X0
       grind)
    | exact superpose eq507015 eq94
    | (have j1 := eq507015 y
       grind)
    | exact resolve eq94 eq507015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507015
  have eq507650 : y = (M.op y y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq507100 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507100
  have eq507851 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq507650
       grind)
    | exact superpose eq507650 eq76
    | exact resolve eq76 eq507650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507970 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq533 y y x
       have i₂ := eq507650
       grind)
    | exact superpose eq507650 eq533
    | exact resolve eq533 eq507650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507650
  have eq508475 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq507970 X0
       have i₂ := eq94 y X0
       grind)
    | exact superpose eq94 eq507970
    | exact resolve eq507970 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507970
  have eq513637 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq507851 X0
       have i₂ := eq508475 X0
       grind)
    | exact superpose eq508475 eq507851
    | exact resolve eq507851 eq508475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507851 eq508475
  have eq514346 : ∀ X0 : G, x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq513637 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513637
  have eq514737 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq42673 x x
       have i₂ := eq514346 X0
       grind)
    | exact superpose eq514346 eq42673
    | (have j0 := eq42673 x x
       have j1 := eq514346 X0
       grind)
    | exact resolve eq42673 eq514346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42673 eq514346
  have eq514766 : ∀ X0 : G, x = (M.op x y) ∨ (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq514737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514737
  have eq514942 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq94 x y
       have i₂ := eq514766 X0
       grind)
    | exact superpose eq514766 eq94
    | (have j1 := eq514766 X0
       grind)
    | exact resolve eq94 eq514766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514766
  have eq515465 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq514942 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514942
  have eq515665 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 x X0
       have i₂ := eq515465 X1
       grind)
    | exact superpose eq515465 eq76
    | (have j1 := eq515465 X1
       grind)
    | exact resolve eq76 eq515465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515710 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23432 x
       have i₂ := eq515465 X0
       grind)
    | exact superpose eq515465 eq23432
    | (have j1 := eq515465 X0
       grind)
    | exact resolve eq23432 eq515465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515784 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq533 x x x
       have i₂ := eq515465 X0
       grind)
    | exact superpose eq515465 eq533
    | (have j1 := eq515465 X1
       grind)
    | exact resolve eq533 eq515465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515465
  have eq516149 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq515710 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515710
  have eq516286 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq515784 X0 X1
       have i₂ := eq94 x X0
       grind)
    | exact superpose eq94 eq515784
    | (have j0 := eq515784 X0 X1
       grind)
    | exact resolve eq515784 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515784
  have eq520661 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 (σ x) X0
       have i₂ := eq516149 X1
       grind)
    | exact superpose eq516149 eq76
    | (have j1 := eq516149 X1
       grind)
    | exact resolve eq76 eq516149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq520780 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq533 (σ x) (σ x) x
       have i₂ := eq516149 X0
       grind)
    | exact superpose eq516149 eq533
    | (have j1 := eq516149 X1
       grind)
    | exact resolve eq533 eq516149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516149
  have eq521289 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq520780 X0 X1
       have i₂ := eq94 (σ x) X0
       grind)
    | exact superpose eq94 eq520780
    | (have j0 := eq520780 X0 X1
       grind)
    | exact resolve eq520780 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520780
  have eq521821 : ∀ X0 X1 X2 : G, (M.op x X0) = X0 ∨ (M.op y X1) = X1 ∨ (M.op y X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq515665 X0 X1
       have i₂ := eq516286 X0 X2
       grind)
    | exact superpose eq516286 eq515665
    | (have j0 := eq515665 X0 X1
       have j1 := eq516286 X0 X1
       grind)
    | exact resolve eq515665 eq516286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515665 eq516286
  have eq522528 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq521821 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521821
  have eq523993 : ∀ X0 X1 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77 y X0
       have i₂ := eq522528 y X1
       grind)
    | exact superpose eq522528 eq77
    | (have j1 := eq522528 X0 X1
       grind)
    | exact resolve eq77 eq522528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525180 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq523993 X0 X1
       have i₂ := eq94 y X0
       grind)
    | exact superpose eq94 eq523993
    | (have j0 := eq523993 X0 X1
       grind)
    | exact resolve eq523993 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq523993
  have eq527885 : ∀ X0 X1 X2 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq525180 X0 X1
       have i₂ := eq522528 X0 X2
       grind)
    | exact superpose eq522528 eq525180
    | (have j0 := eq525180 X0 X1
       have j1 := eq522528 X0 X1
       grind)
    | exact resolve eq525180 eq522528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522528 eq525180
  have eq528846 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq527885 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527885
  have eq532581 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq528846 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528846
  have eq532582 : y = (M.op x y) := by grind
  clear eq532581
  have eq1049991 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = X0 ∨ (M.op y X1) = X1 ∨ (M.op y X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq520661 X0 X1
       have i₂ := eq521289 X0 X2
       grind)
    | exact superpose eq521289 eq520661
    | (have j0 := eq520661 X0 X1
       have j1 := eq521289 X0 X1
       grind)
    | exact resolve eq520661 eq521289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520661 eq521289
  have eq1051087 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1049991 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049991
  have eq1051212 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1051087 X0 (σ y)
       grind)
    | exact superpose eq1051087 eq16
    | (have j1 := eq1051087 X0 x
       grind)
    | exact resolve eq16 eq1051087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051087
  have eq1053213 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1051212 X0
       have i₂ := eq532582
       grind)
    | exact superpose eq532582 eq1051212
    | (have j0 := eq1051212 X0
       grind)
    | exact resolve eq1051212 eq532582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532582 eq1051212
  have eq1053214 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1053213 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053213
  have eq1055227 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq23432 y
       have i₂ := eq1053214 y
       grind)
    | exact superpose eq1053214 eq23432
    | exact resolve eq23432 eq1053214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23432
  have eq1055303 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq533 y X1 X0
       have i₂ := eq1053214 X0
       grind)
    | exact superpose eq1053214 eq533
    | exact resolve eq533 eq1053214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq1056055 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq77 y X0
       have i₂ := eq1053214 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq1053214 eq77
    | exact resolve eq77 eq1053214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1057084 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1055227
  have eq1057734 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq1056055 X0
       have i₂ := eq1053214 y
       grind)
    | exact superpose eq1053214 eq1056055
    | exact resolve eq1056055 eq1053214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056055
  have eq1058293 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1055303 X0 X0
       have i₂ := eq1053214 X0
       grind)
    | exact superpose eq1053214 eq1055303
    | exact resolve eq1055303 eq1053214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055303
  have eq1058771 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1057734 X0
       have i₂ := eq1053214 X0
       grind)
    | exact superpose eq1053214 eq1057734
    | exact resolve eq1057734 eq1053214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053214 eq1057734
  have eq1152556 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq1057084
       grind)
    | exact superpose eq1057084 eq9
    | exact resolve eq9 eq1057084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057084
  have eq1153555 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1152556 X0
       have i₂ := eq1058293 X0 (σ y)
       grind)
    | exact superpose eq1058293 eq1152556
    | exact resolve eq1152556 eq1058293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152556
  have eq1154563 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1058293 X0 (σ y)
       have i₂ := eq1153555 X0
       grind)
    | exact superpose eq1153555 eq1058293
    | exact resolve eq1058293 eq1153555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058293 eq1153555
  have eq1160912 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1154563 (σ x)
       grind)
    | exact superpose eq1154563 eq16
    | exact resolve eq16 eq1154563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154563
  have eq1161253 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1160912
       have i₂ := eq1058771 x
       grind)
    | exact superpose eq1058771 eq1160912
    | exact resolve eq1160912 eq1058771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058771 eq1160912
  have eq1161254 : False := by grind
  exact eq1161254

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
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
  have eq180 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq199 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq634 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq820 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq632
       grind)
    | exact superpose eq632 eq39
    | exact resolve eq39 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq821 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq820
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq820
    | exact resolve eq820 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq823 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq821
    | exact resolve eq821 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq893 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq199
    | exact resolve eq199 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq917 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq893 X0
       grind)
    | exact superpose eq893 eq16
    | exact resolve eq16 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq978 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq177 eq917
    | exact resolve eq917 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq982 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq178 eq917
    | exact resolve eq917 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq917
  have eq1703 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq823 eq634
    | exact resolve eq634 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq1710 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1703
       have r₂ := eq27
       grind)
    | exact resolve eq1703 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703
  have eq1716 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1710 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1710
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1710
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1710
       grind)
    | exact resolve eq12 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710
  have eq1727 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1716
  have eq1733 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1727
    | exact resolve eq1727 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq1734 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1733
  have eq1746 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1734 eq107
    | exact resolve eq107 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1734
  have eq1753 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1746
    | exact resolve eq1746 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746
  have eq1756 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq632 eq1753
    | exact resolve eq1753 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq1757 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1756
  have eq1764 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1757
       grind)
    | exact superpose eq1757 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1757
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1757
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1757
       grind)
    | exact resolve eq12 eq1757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1765 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1757
       grind)
    | exact superpose eq1757 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1757
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1757
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1757
       grind)
    | exact resolve eq13 eq1757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq1774 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1765
  have eq1775 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1764
  have eq1780 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1774
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1774
    | exact resolve eq1774 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774
  have eq1781 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1775
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1775
    | exact resolve eq1775 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775
  have eq1782 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1781
  have eq1828 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1780
       grind)
    | exact superpose eq1780 eq40
    | exact resolve eq40 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1780
  have eq1829 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1828
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1828
    | exact resolve eq1828 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq1831 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1829
    | exact resolve eq1829 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829
  have eq1874 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq1782
       grind)
    | exact superpose eq1782 eq36
    | exact resolve eq36 eq1782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1782
  have eq1883 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1874
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1874
    | exact resolve eq1874 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874
  have eq2048 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1883 eq634
    | exact resolve eq634 eq1883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634 eq1883
  have eq2057 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2048
  have eq2104 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2057 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2057
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2057
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2057
       grind)
    | exact resolve eq13 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq2114 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2104
  have eq2121 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2114
    | exact resolve eq2114 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2114
  have eq2123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1831 eq2121
    | exact resolve eq2121 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831 eq2121
  have eq2125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2123
       have r₂ := eq27
       grind)
    | exact resolve eq2123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123
  have eq2130 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2125 eq190
    | exact resolve eq190 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq2146 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2125 eq982
    | exact resolve eq982 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq2160 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2146 eq2130
    | exact resolve eq2130 eq2146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq2164 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2160
    | exact resolve eq2160 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160
  have eq2165 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2125 eq2164
    | exact resolve eq2164 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125 eq2164
  have eq2167 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2165 eq31
    | exact resolve eq31 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2165
  have eq2233 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2167
    | exact resolve eq2167 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167
  have eq2239 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq2233
       grind)
    | exact superpose eq2233 eq18
    | exact resolve eq18 eq2233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2251 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq978
       have i₂ := eq2233
       grind)
    | exact superpose eq2233 eq978
    | exact resolve eq978 eq2233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2296 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2146 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq2146
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2146
       grind)
    | exact resolve eq13 eq2146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2309 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2296
  have eq2317 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2309 eq141
    | exact resolve eq141 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq2309
  have eq2330 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2317
    | exact resolve eq2317 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2317
  have eq2354 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq2251 eq183
    | exact resolve eq183 eq2251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq2251
  have eq2371 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2239 eq2354
    | exact resolve eq2354 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239 eq2354
  have eq2406 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq2371
  have eq2407 : x = y := by
    first
    | (have r₁ := eq2406
       have r₂ := eq2233
       grind)
    | exact resolve eq2406 eq2233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2233 eq2406
  have eq2412 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2407
       grind)
    | exact superpose eq2407 eq18
    | exact resolve eq18 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2413 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2407
       grind)
    | exact superpose eq2407 eq24
    | exact resolve eq24 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2426 : (M.op x y) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq632
       have i₂ := eq2407
       grind)
    | exact superpose eq2407 eq632
    | exact resolve eq632 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq2447 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2330 eq2426
    | exact resolve eq2426 eq2330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2330 eq2426
  have eq2448 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq2447
  have eq2451 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2413
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2413
    | exact resolve eq2413 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2413
  have eq2453 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2448
       have i₂ := eq2412
       grind)
    | exact superpose eq2412 eq2448
    | exact resolve eq2448 eq2412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412 eq2448
  have eq2454 : x = (M.op x y) := by grind
  clear eq2453
  have eq2455 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2451 eq26
    | exact resolve eq26 eq2451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2451
  have eq2520 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq180
       have i₂ := eq2454
       grind)
    | exact superpose eq2454 eq180
    | (have r₁ := eq180
       have r₂ := eq2454
       grind)
    | exact resolve eq180 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq2531 : (k y (M.op x y)) = (M.op y (M.op x y)) := by grind
  clear eq2520
  have eq2536 : (k x (M.op x y)) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2531
       have i₂ := eq2407
       grind)
    | exact superpose eq2407 eq2531
    | exact resolve eq2531 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2407 eq2531
  have eq2542 : (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq978 eq2536
    | exact resolve eq2536 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978 eq2536
  have eq2546 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2542
       have i₂ := eq2454
       grind)
    | exact superpose eq2454 eq2542
    | exact resolve eq2542 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542
  have eq2685 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2455 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq2455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2687 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2455 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq2455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2455
  have eq2700 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2685
  have eq2703 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq2700
       have r₂ := eq2687
       grind)
    | exact resolve eq2700 eq2687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2687 eq2700
  have eq3640 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2703 eq97
    | exact resolve eq97 eq2703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq2703
  have eq3656 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3640
       have i₂ := eq2454
       grind)
    | exact superpose eq2454 eq3640
    | exact resolve eq3640 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454 eq3640
  have eq3659 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2546 eq3656
    | exact resolve eq3656 eq2546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2546 eq3656
  have eq3668 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3659 eq14
    | exact resolve eq14 eq3659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3659
  have eq3669 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3668
    | exact resolve eq3668 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3668
  have eq3672 : False := by grind
  exact eq3672

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
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
  have eq181 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq645 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq645
       grind)
    | exact superpose eq645 eq40
    | exact resolve eq40 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq645
  have eq716 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq715
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq715
    | exact resolve eq715 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq718 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq716
    | exact resolve eq716 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq718 eq659
    | exact resolve eq659 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659 eq718
  have eq735 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq728
       have r₂ := eq27
       grind)
    | exact resolve eq728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq742 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq735 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq735
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq735
       grind)
    | exact resolve eq13 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq735 eq16
    | exact resolve eq16 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq742
  have eq750 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq745 eq91
    | exact resolve eq91 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq745
  have eq753 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq750
    | exact resolve eq750 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq805 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq735 eq743
    | exact resolve eq743 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq570 eq743
    | exact resolve eq743 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq743
  have eq818 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq805
  have eq820 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq809 eq818
    | exact resolve eq818 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq818
  have eq835 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq820 eq735
    | exact resolve eq735 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq820
  have eq843 : y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq835
  have eq854 : y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq843
       grind)
    | exact superpose eq843 eq584
    | exact resolve eq584 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq859 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq843
       grind)
    | exact superpose eq843 eq16
    | exact resolve eq16 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq859 X0
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq859
    | exact resolve eq859 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq859
  have eq938 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq862 y
       have i₂ := eq854
       grind)
    | exact superpose eq854 eq862
    | exact resolve eq862 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq862
  have eq948 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq938
  have eq953 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq843
       have i₂ := eq948
       grind)
    | exact superpose eq948 eq843
    | exact resolve eq843 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843 eq948
  have eq962 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq953
  have eq1198 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq962 eq32
    | exact resolve eq32 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq962
  have eq1240 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq1198
    | exact resolve eq1198 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1198
  have eq1241 : x = y := by grind
  clear eq1240
  have eq1245 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1241
       grind)
    | exact superpose eq1241 eq18
    | exact resolve eq18 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1246 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1241
       grind)
    | exact superpose eq1241 eq24
    | exact resolve eq24 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1259 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq753
       have i₂ := eq1241
       grind)
    | exact superpose eq1241 eq753
    | exact resolve eq753 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq1268 : x = (M.op x x) := by
    first
    | (have j1 := eq668 x
       grind)
    | (have r₁ := eq1259
       have r₂ := eq668 x
       grind)
    | exact resolve eq1259 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq1259
  have eq1271 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1246
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1246
    | exact resolve eq1246 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1246
  have eq1272 : x = (M.op x y) := by
    first
    | (have i₁ := eq1268
       have i₂ := eq1245
       grind)
    | exact superpose eq1245 eq1268
    | exact resolve eq1268 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245 eq1268
  have eq1273 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1271 eq26
    | exact resolve eq26 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1271
  have eq1359 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq181
       have i₂ := eq1272
       grind)
    | exact superpose eq1272 eq181
    | (have r₁ := eq181
       have r₂ := eq1272
       grind)
    | exact resolve eq181 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1366 : (M.op x y) = (k y (M.op x y)) := by grind
  clear eq1359
  have eq1369 : (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq1366
       have i₂ := eq1241
       grind)
    | exact superpose eq1241 eq1366
    | exact resolve eq1366 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241 eq1366
  have eq1374 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1369
       have i₂ := eq1272
       grind)
    | exact superpose eq1272 eq1369
    | exact resolve eq1369 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1475 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1273 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1478 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1273 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1273
  have eq1483 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq1475
       have r₂ := eq1478
       grind)
    | exact resolve eq1475 eq1478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475 eq1478
  have eq1511 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1483 eq98
    | exact resolve eq98 eq1483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq1483
  have eq1518 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1511
       have i₂ := eq1272
       grind)
    | exact superpose eq1272 eq1511
    | exact resolve eq1511 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272 eq1511
  have eq1521 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1374 eq1518
    | exact resolve eq1518 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374 eq1518
  have eq1529 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1521 eq14
    | exact resolve eq14 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq1530 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1529
    | exact resolve eq1529 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1529
  have eq1533 : False := by grind
  exact eq1533

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
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
  have eq182 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) ≠ X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
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
  have eq645 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq645
       grind)
    | exact superpose eq645 eq40
    | exact resolve eq40 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq716 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq715
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq715
    | exact resolve eq715 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq718 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq716
    | exact resolve eq716 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq718 eq659
    | exact resolve eq659 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq735 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq728
       have r₂ := eq27
       grind)
    | exact resolve eq728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq740 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq735 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq735
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq735
       grind)
    | exact resolve eq12 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq735 eq16
    | exact resolve eq16 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq740
  have eq747 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq746
    | exact resolve eq746 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq766 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq747 eq142
    | exact resolve eq142 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq747
  have eq769 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq766
    | exact resolve eq766 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq766
  have eq772 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq645 eq769
    | exact resolve eq769 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq769
  have eq788 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq772
       grind)
    | exact superpose eq772 eq584
    | exact resolve eq584 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq772
       grind)
    | exact superpose eq772 eq16
    | exact resolve eq16 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq796 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq793 X0
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq793
    | exact resolve eq793 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq1712 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq796 y
       have i₂ := eq788
       grind)
    | exact superpose eq788 eq796
    | exact resolve eq796 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq1718 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq562 x
       have i₂ := eq796 y
       grind)
    | exact superpose eq796 eq562
    | exact resolve eq562 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1731 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1712
  have eq1737 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1718
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1718
    | exact resolve eq1718 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq1758 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq796 x
       have i₂ := eq1731
       grind)
    | exact superpose eq1731 eq796
    | exact resolve eq796 eq1731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq1731
  have eq1772 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1758
  have eq1805 : y = (M.op (M.op (M.op x y) x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq1772
       grind)
    | exact superpose eq1772 eq175
    | exact resolve eq175 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772
  have eq1815 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1737 eq1805
    | exact resolve eq1805 eq1737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737 eq1805
  have eq1816 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1815
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1815
    | exact resolve eq1815 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815
  have eq1817 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1816
  have eq1819 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1817 eq27
    | exact resolve eq27 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1822 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1817 eq182
    | (have r₁ := eq182
       have r₂ := eq1817
       grind)
    | exact resolve eq182 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq1817
  have eq1828 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1822
  have eq1835 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1828 eq718
    | exact resolve eq718 eq1828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq1828
  have eq1842 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1835
       have r₂ := eq1819
       grind)
    | exact resolve eq1835 eq1819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1819 eq1835
  have eq1862 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq1842
       grind)
    | exact superpose eq1842 eq584
    | exact resolve eq584 eq1842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1866 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq1842
       grind)
    | exact superpose eq1842 eq16
    | exact resolve eq16 eq1842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842
  have eq1883 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1866 X0
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq1866
    | exact resolve eq1866 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866
  have eq1977 : x = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1883 y
       have i₂ := eq1862
       grind)
    | exact superpose eq1862 eq1883
    | exact resolve eq1883 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq1999 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq1977
  have eq2024 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq1999
       grind)
    | exact superpose eq1999 eq16
    | exact resolve eq16 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999
  have eq2044 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1883 eq2024
    | exact resolve eq2024 eq1883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883 eq2024
  have eq2369 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2044 y
       grind)
    | exact superpose eq2044 eq18
    | (have j1 := eq2044 y
       grind)
    | exact resolve eq18 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2044
  have eq2382 : y = (M.op x y) := by grind
  clear eq2369
  have eq2388 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2382
       grind)
    | exact superpose eq2382 eq18
    | exact resolve eq18 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2389 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2382
       grind)
    | exact superpose eq2382 eq24
    | exact resolve eq24 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2390 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq2382
       grind)
    | exact superpose eq2382 eq37
    | exact resolve eq37 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq2392 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op x X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq2382
       grind)
    | exact superpose eq2382 eq175
    | exact resolve eq175 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2399 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq584 X0
       have i₂ := eq2382
       grind)
    | exact superpose eq2382 eq584
    | exact resolve eq584 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq2415 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2389 eq20
    | exact resolve eq20 eq2389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2418 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq2389 eq15
    | exact resolve eq15 eq2389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2657 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op (M.op x y) (M.op x X0))) ∨ (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq2392 eq28
    | (have j0 := eq28 (M.op x y) (M.op (M.op x y) (M.op x X0))
       grind)
    | exact resolve eq28 eq2392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2392
  have eq2664 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x X0)) ∨ (M.op x y) = (k (M.op x y) (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq2399 eq2657
    | (have j0 := eq2657 X0
       grind)
    | exact resolve eq2657 eq2399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2657
  have eq3121 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) (M.op x X0)) ∨ (M.op x y) = (k (M.op x y) (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq2388 eq183
    | exact resolve eq183 eq2388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq3230 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have j0 := eq3121 X0
       have j1 := eq2664 X0
       grind)
    | (have r₁ := eq3121 X0
       have r₂ := eq2664 X0
       grind)
    | exact resolve eq3121 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2664 eq3121
  have eq3485 : (M.op x y) = (k (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2388 eq3230
    | (have j0 := eq3230 y
       grind)
    | exact resolve eq3230 eq2388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3230
  have eq3503 : (σ (M.op x y)) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq3485 eq2390
    | exact resolve eq2390 eq3485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2390 eq3485
  have eq3510 : (σ (M.op x y)) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq3503
    | exact resolve eq3503 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3503
  have eq3512 : (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq2415 eq3510
    | exact resolve eq3510 eq2415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3510
  have eq7362 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq735 eq743
    | exact resolve eq743 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7379 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq570 eq743
    | exact resolve eq743 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq743
  have eq7408 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq7362
  have eq7428 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq7379
       have i₂ := eq2382
       grind)
    | exact superpose eq2382 eq7379
    | exact resolve eq7379 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7379
  have eq7433 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq7408
       have i₂ := eq2382
       grind)
    | exact superpose eq2382 eq7408
    | exact resolve eq7408 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7408
  have eq7438 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq7428 eq7433
    | exact resolve eq7433 eq7428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7428 eq7433
  have eq7479 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq7438 eq735
    | exact resolve eq735 eq7438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq7438
  have eq7512 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq7479
       have i₂ := eq2382
       grind)
    | exact superpose eq2382 eq7479
    | exact resolve eq7479 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2382 eq7479
  have eq7513 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by grind
  clear eq7512
  have eq7537 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7513 eq2399
    | exact resolve eq2399 eq7513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7542 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq7513 eq16
    | exact resolve eq16 eq7513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7573 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2399 eq7542
    | exact resolve eq7542 eq2399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399 eq7542
  have eq7982 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7537 eq7573
    | exact resolve eq7573 eq7537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7537 eq7573
  have eq8025 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by grind
  clear eq7982
  have eq8035 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7513 eq8025
    | exact resolve eq8025 eq7513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7513 eq8025
  have eq8103 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8035 eq2418
    | exact resolve eq2418 eq8035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418 eq8035
  have eq8119 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq8103
    | exact resolve eq8103 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq8103
  have eq8120 : x = (M.op x y) := by grind
  clear eq8119
  have eq8161 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq8120
       grind)
    | exact superpose eq8120 eq22
    | exact resolve eq22 eq8120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq8221 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2388
       have i₂ := eq8120
       grind)
    | exact superpose eq8120 eq2388
    | exact resolve eq2388 eq8120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2388 eq8120
  have eq8258 : (σ x) = (σ y) := by
    first
    | exact superpose eq8161 eq2389
    | exact resolve eq2389 eq8161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389
  have eq8259 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8161 eq20
    | exact resolve eq20 eq8161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8161
  have eq8295 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8258 eq26
    | exact resolve eq26 eq8258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq8359 : (σ x) = (k (σ x) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq8258 eq3512
    | exact resolve eq3512 eq8258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3512
  have eq8369 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq8221 eq8359
    | exact resolve eq8359 eq8221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8221 eq8359
  have eq8391 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq8369
    | exact resolve eq8369 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8369
  have eq8406 : (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq2415 eq8391
    | exact resolve eq8391 eq2415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415 eq8391
  have eq8412 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq8258 eq8406
    | exact resolve eq8406 eq8258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8258 eq8406
  have eq8582 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8295 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq8295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq8295
  have eq8604 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8412 eq8582
    | exact resolve eq8582 eq8412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8412 eq8582
  have eq8605 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8604
  have eq8608 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq8605 eq27
    | exact resolve eq27 eq8605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq8605
  have eq8632 : False := by grind
  exact eq8632

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pyx_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
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
  have eq134 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
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
  have eq181 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq386 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
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
  have eq645 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq679 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq715 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq645
       grind)
    | exact superpose eq645 eq40
    | exact resolve eq40 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq716 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq715
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq715
    | exact resolve eq715 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq718 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq716
    | exact resolve eq716 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq718 eq659
    | exact resolve eq659 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq735 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq728
       have r₂ := eq27
       grind)
    | exact resolve eq728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq742 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq735 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq735
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq735
       grind)
    | exact resolve eq13 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq745 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq742
  have eq749 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq745 eq91
    | exact resolve eq91 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq745
  have eq752 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq749
    | exact resolve eq749 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq1559 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq698 x y
       have i₂ := eq752
       grind)
    | exact superpose eq752 eq698
    | (have j0 := eq698 x y
       grind)
    | (have r₁ := eq698 x y
       have r₂ := eq752
       grind)
    | exact resolve eq698 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq1591 : x = (M.op x y) ∨ x = (k y x) ∨ y = (M.op y x) := by grind
  clear eq1559
  have eq1601 : x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1591
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq1591
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1591 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1591
  have eq1605 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1601
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1601
    | exact resolve eq1601 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1607 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq645
       have i₂ := eq1605
       grind)
    | exact superpose eq1605 eq645
    | exact resolve eq645 eq1605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq1605
  have eq1612 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1607
  have eq1623 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq1612
       grind)
    | exact superpose eq1612 eq584
    | exact resolve eq584 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1627 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq1612
       grind)
    | exact superpose eq1612 eq16
    | exact resolve eq16 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1641 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1627 X0
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq1627
    | exact resolve eq1627 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq1627
  have eq1662 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1623
       grind)
    | exact superpose eq1623 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1623
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1623
       grind)
    | exact resolve eq13 eq1623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1669 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq1662
  have eq1724 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1641 y
       have i₂ := eq1623
       grind)
    | exact superpose eq1623 eq1641
    | exact resolve eq1641 eq1623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq1744 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1724
  have eq1758 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1612
       have i₂ := eq1744
       grind)
    | exact superpose eq1744 eq1612
    | exact resolve eq1612 eq1744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq1766 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq1744
       grind)
    | exact superpose eq1744 eq16
    | exact resolve eq16 eq1744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744
  have eq1774 : x = (M.op x y) ∨ x = y := by grind
  clear eq1758
  have eq1784 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1641 eq1766
    | exact resolve eq1766 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641 eq1766
  have eq1879 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1784 y
       grind)
    | exact superpose eq1784 eq18
    | (have j1 := eq1784 y
       grind)
    | exact resolve eq18 eq1784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1784
  have eq1898 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1879
       grind)
    | exact superpose eq1879 eq24
    | exact resolve eq24 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1934 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1669
       have i₂ := eq1879
       grind)
    | exact superpose eq1879 eq1669
    | exact resolve eq1669 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq1937 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1934
  have eq1957 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1898
    | exact resolve eq1898 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq1967 : (k (M.op x y) (M.op x y)) = (τ (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1957 eq134
    | exact resolve eq134 eq1957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq1957
  have eq1973 : (k y y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116 eq1967
    | exact resolve eq1967 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1967
  have eq1983 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1669 eq1973
    | exact resolve eq1973 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669 eq1973
  have eq1991 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1774 eq1983
    | exact resolve eq1983 eq1774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774 eq1983
  have eq1995 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1937 eq1991
    | exact resolve eq1991 eq1937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937 eq1991
  have eq1996 : x = (M.op x y) := by grind
  clear eq1995
  have eq1998 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1996
       grind)
    | exact superpose eq1996 eq22
    | exact resolve eq22 eq1996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1999 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq1996
       grind)
    | exact superpose eq1996 eq36
    | exact resolve eq36 eq1996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq2003 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq181
       have i₂ := eq1996
       grind)
    | exact superpose eq1996 eq181
    | (have r₁ := eq181
       have r₂ := eq1996
       grind)
    | exact resolve eq181 eq1996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq1996
  have eq2023 : (M.op x y) = (k y (M.op x y)) := by grind
  clear eq2003
  have eq2044 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1998 eq20
    | exact resolve eq20 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2055 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq1998 eq386
    | exact resolve eq386 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq1998
  have eq2119 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2023 eq37
    | exact resolve eq37 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2023
  have eq2124 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq2119
    | exact resolve eq2119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2119
  have eq2126 : (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2044 eq2124
    | exact resolve eq2124 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq2366 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2126 eq659
    | exact resolve eq659 eq2126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq2372 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq2126 eq698
    | (have j0 := eq698 (σ y) (σ x)
       grind)
    | (have r₁ := eq698 (σ y) (σ x)
       have r₂ := eq2126
       grind)
    | exact resolve eq698 eq2126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq2126
  have eq2373 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq2372
  have eq2486 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2366 eq16
    | exact resolve eq16 eq2366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2487 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2366 eq16
    | exact resolve eq16 eq2366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3532 : (τ (σ y)) = (k (M.op x y) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2373 eq2055
    | exact resolve eq2055 eq2373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2373
  have eq3544 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq32 eq3532
    | exact resolve eq3532 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3532
  have eq3552 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq3544 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3544
       grind)
    | exact resolve eq13 eq3544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3544
  have eq3567 : (σ y) = (k (σ x) (σ y)) ∨ y = (k (M.op x y) y) := by grind
  clear eq3552
  have eq3571 : (τ (σ y)) = (k (M.op x y) (τ (σ y))) ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq3567 eq2055
    | exact resolve eq2055 eq3567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055 eq3567
  have eq3580 : y = (k (M.op x y) y) ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq32 eq3571
    | exact resolve eq3571 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3571
  have eq3581 : y = (k (M.op x y) y) := by grind
  clear eq3580
  have eq3587 : (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq3581 eq1999
    | exact resolve eq1999 eq3581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999 eq3581
  have eq3596 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3587
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3587
    | exact resolve eq3587 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3587
  have eq5182 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2366 eq2486
    | exact resolve eq2486 eq2366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486
  have eq5221 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5182
  have eq5277 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq570 eq2487
    | exact resolve eq2487 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq2487
  have eq5315 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5277 eq5221
    | exact resolve eq5221 eq5277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5221 eq5277
  have eq5342 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5315
  have eq5363 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5342 eq2366
    | exact resolve eq2366 eq5342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366 eq5342
  have eq5394 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5363
  have eq5412 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5394 eq27
    | exact resolve eq27 eq5394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5394
  have eq5423 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5412
       have r₂ := eq2044
       grind)
    | exact resolve eq5412 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5412
  have eq5424 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5423 eq26
    | exact resolve eq26 eq5423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq5479 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq5423 eq3596
    | exact resolve eq3596 eq5423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3596 eq5423
  have eq5592 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5424 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq5424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5424
  have eq5613 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5479 eq5592
    | exact resolve eq5592 eq5479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5479 eq5592
  have eq5614 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5613
  have eq5618 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5614 eq27
    | exact resolve eq27 eq5614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5614
  have eq5632 : False := by grind
  exact eq5632

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq174 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq175 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq177 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq179 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq180 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
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
    | (have i₁ := eq176 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq187 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq194 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq190 eq16
    | exact resolve eq16 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq183 eq187
    | exact resolve eq187 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq560 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
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
  have eq567 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq190 eq194
    | exact resolve eq194 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq571 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq567 eq16
    | exact resolve eq16 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq579 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq560 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq560
    | exact resolve eq560 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq606 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq608 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq571 (M.op sF3 x)
       have i₂ := eq16 sF3 sF3 x
       grind)
    | exact superpose eq16 eq571
    | exact resolve eq571 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq923 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq606
       grind)
    | exact superpose eq606 eq39
    | exact resolve eq39 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq924 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq923
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq923
    | exact resolve eq923 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq926 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq924
    | exact resolve eq924 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq988 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 X0 x x X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1015 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq988 (M.op X0 X1)
       grind)
    | exact superpose eq988 eq178
    | exact resolve eq178 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1020 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq988 X0
       grind)
    | exact superpose eq988 eq16
    | exact resolve eq16 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1174 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1020 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq1020
    | exact resolve eq1020 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1177 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq179 eq1020
    | exact resolve eq1020 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1180 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq180 eq1020
    | exact resolve eq1020 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq1020
  have eq1197 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1177 eq11
    | (have j0 := eq11 (M.op x y) x
       grind)
    | exact resolve eq11 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1199 : x ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq1177 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq1197
       have r₂ := eq1199
       grind)
    | exact resolve eq1197 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1367 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1205 eq39
    | exact resolve eq39 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1368 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq20 eq1367
    | exact resolve eq1367 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq2311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq926 eq608
    | exact resolve eq608 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2323 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2311
       have r₂ := eq27
       grind)
    | exact resolve eq2311 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2311
  have eq2329 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2323 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2323
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2323
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2323
       grind)
    | exact resolve eq12 eq2323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq2343 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq2329
  have eq2350 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2343
       have r₂ := eq175
       grind)
    | exact resolve eq2343 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2343
  have eq2352 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq2350
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq2350
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq2350
       have r₂ := eq13 y x
       grind)
    | exact resolve eq2350 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq2355 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2352 eq926
    | exact resolve eq926 eq2352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq2359 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2352 eq141
    | exact resolve eq141 eq2352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352
  have eq2362 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2355
  have eq2366 : y = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq2359
    | exact resolve eq2359 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2359
  have eq2369 : y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq2366
       have r₂ := eq174
       grind)
    | exact resolve eq2366 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366
  have eq2373 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq606
       have i₂ := eq2369
       grind)
    | exact superpose eq2369 eq606
    | exact resolve eq606 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq2369
  have eq2380 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2373
  have eq2410 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq2362
       grind)
    | exact superpose eq2362 eq16
    | exact resolve eq16 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2420 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1174 y x
       have i₂ := eq2362
       grind)
    | exact superpose eq2362 eq1174
    | exact resolve eq1174 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2428 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2410 X0
       have i₂ := eq579 X0
       grind)
    | exact superpose eq579 eq2410
    | exact resolve eq2410 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq2410
  have eq2463 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2380
       grind)
    | exact superpose eq2380 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2380
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2380
       grind)
    | exact resolve eq12 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380
  have eq2477 : x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2463
  have eq2484 : x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2477
       have r₂ := eq174
       grind)
    | exact resolve eq2477 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477
  have eq2487 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq2484
       have r₂ := eq13 y x
       grind)
    | exact resolve eq2484 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2484
  have eq2491 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq2487
       grind)
    | exact superpose eq2487 eq39
    | exact resolve eq39 eq2487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2487
  have eq2498 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2491
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2491
    | exact resolve eq2491 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491
  have eq3295 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2428 y
       have i₂ := eq2420
       grind)
    | exact superpose eq2420 eq2428
    | exact resolve eq2428 eq2420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420
  have eq3326 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3295
  have eq3339 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2362
       have i₂ := eq3326
       grind)
    | exact superpose eq3326 eq2362
    | exact resolve eq2362 eq3326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362
  have eq3346 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq3326
       grind)
    | exact superpose eq3326 eq16
    | exact resolve eq16 eq3326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326
  have eq3360 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq3339
  have eq3371 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2428 eq3346
    | exact resolve eq3346 eq2428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2428 eq3346
  have eq3400 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq3360 eq1368
    | exact resolve eq1368 eq3360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368 eq3360
  have eq3404 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2498 eq3400
    | exact resolve eq3400 eq2498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2498 eq3400
  have eq3405 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq3404
  have eq3846 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3371 y
       grind)
    | exact superpose eq3371 eq18
    | (have j1 := eq3371 y
       grind)
    | exact resolve eq18 eq3371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371
  have eq3904 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3846 eq28
    | exact resolve eq28 eq3846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3846
  have eq3932 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq3904
    | exact resolve eq3904 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904
  have eq3933 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3932
  have eq3945 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3933
       grind)
    | exact superpose eq3933 eq24
    | exact resolve eq24 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4004 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3945
    | exact resolve eq3945 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3945
  have eq4991 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3405 eq141
    | exact resolve eq141 eq3405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq3405
  have eq5000 : y = (k y x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq4991
    | exact resolve eq4991 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4991
  have eq5003 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq5000
       have r₂ := eq174
       grind)
    | exact resolve eq5000 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5000
  have eq5029 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (k y x) := by
    first
    | exact superpose eq5003 eq1015
    | exact resolve eq1015 eq5003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq5037 : x = (M.op (M.op x y) x) ∨ y = (k y x) := by
    first
    | exact superpose eq1177 eq5029
    | exact resolve eq5029 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5029
  have eq5048 : x = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq5003 eq5037
    | exact resolve eq5037 eq5003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5003 eq5037
  have eq5053 : y = (k y x) := by
    first
    | (have r₁ := eq5048
       have r₂ := eq174
       grind)
    | exact resolve eq5048 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq5048
  have eq5055 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5053
       have i₂ := eq3933
       grind)
    | exact superpose eq3933 eq5053
    | exact resolve eq5053 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5060 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq5053
       grind)
    | exact superpose eq5053 eq39
    | exact resolve eq39 eq5053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5053
  have eq5067 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5060
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5060
    | exact resolve eq5060 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5060
  have eq5070 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have r₁ := eq5055
       have r₂ := eq1199
       grind)
    | exact resolve eq5055 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199 eq5055
  have eq5078 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5067 eq608
    | exact resolve eq608 eq5067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq5067
  have eq5093 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq5070 eq39
    | exact resolve eq39 eq5070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq5070
  have eq5098 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq5093
    | exact resolve eq5093 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5093
  have eq5109 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq5098 eq663
    | (have j0 := eq663 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq663 eq5098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq5098
  have eq5189 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq5078 eq16
    | exact resolve eq16 eq5078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5206 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5078 eq1174
    | exact resolve eq1174 eq5078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq5218 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq772 eq5189
    | exact resolve eq5189 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772 eq5189
  have eq6908 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5206 eq5218
    | exact resolve eq5218 eq5206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5206 eq5218
  have eq6947 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6908
  have eq6959 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6947 eq5078
    | exact resolve eq5078 eq6947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5078 eq6947
  have eq6992 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6959
  have eq7029 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6992 eq27
    | exact resolve eq27 eq6992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6992
  have eq7069 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4004 eq7029
    | (have r₁ := eq7029
       have r₂ := eq4004
       grind)
    | exact resolve eq7029 eq4004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4004 eq7029
  have eq7074 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7069
  have eq7082 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7074 eq190
    | exact resolve eq190 eq7074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq7102 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7074 eq1180
    | exact resolve eq1180 eq7074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq7136 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7102 eq7082
    | exact resolve eq7082 eq7102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7082 eq7102
  have eq7141 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7136
    | exact resolve eq7136 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7136
  have eq7142 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7074 eq7141
    | exact resolve eq7141 eq7074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7074 eq7141
  have eq7143 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7142
  have eq7145 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7143 eq31
    | exact resolve eq31 eq7143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq7143
  have eq7284 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq7145
    | exact resolve eq7145 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq7145
  have eq7303 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3933 eq7284
    | exact resolve eq7284 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3933 eq7284
  have eq7304 : x = (M.op x y) := by grind
  clear eq7303
  have eq7309 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7304
       grind)
    | exact superpose eq7304 eq18
    | exact resolve eq18 eq7304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7310 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq7304
       grind)
    | exact superpose eq7304 eq22
    | exact resolve eq22 eq7304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq7321 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1177
       have i₂ := eq7304
       grind)
    | exact superpose eq7304 eq1177
    | exact resolve eq1177 eq7304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177 eq7304
  have eq7352 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7310 eq20
    | exact resolve eq20 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq7454 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7352 eq5109
    | (have r₁ := eq5109
       have r₂ := eq7352
       grind)
    | exact resolve eq5109 eq7352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5109
  have eq7457 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7454
  have eq7458 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7457
  have eq7562 : y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq7321 eq183
    | exact resolve eq183 eq7321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq7321
  have eq7614 : y = (M.op x y) := by
    first
    | exact superpose eq7309 eq7562
    | exact resolve eq7562 eq7309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7309 eq7562
  have eq7627 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq7614
       grind)
    | exact superpose eq7614 eq24
    | exact resolve eq24 eq7614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7614
  have eq7695 : (σ x) = (σ y) := by
    first
    | exact superpose eq7310 eq7627
    | exact resolve eq7627 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7310 eq7627
  have eq7710 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7695 eq26
    | exact resolve eq26 eq7695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq7695
  have eq7828 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7458 eq7710
    | exact resolve eq7710 eq7458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7458 eq7710
  have eq7863 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq7828 eq27
    | exact resolve eq27 eq7828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq7828
  have eq7923 : False := by grind
  exact eq7923

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pyx_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq65 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq69 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by
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
  have eq71 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 ∨ (M.op (M.op X1 X0) (M.op X1 X2)) = (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) ∨ (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq71 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq78 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq80 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq85 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq114 : (k (σ y) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq11 y sF0
       grind)
    | exact superpose eq11 eq80
    | (have j1 := eq11 y (M.op x y)
       grind)
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq123 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
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
  have eq130 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq141 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq130 eq16
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq212 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq237 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op x X0) (M.op x y))) = X0 ∨ (M.op (M.op x X0) (M.op x y)) = (k (M.op (M.op x X0) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq53 eq12
    | (have j0 := eq12 (M.op (M.op x X0) (M.op x y)) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op x X0) (M.op x y)) X0
       have r₂ := eq53 X0
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (k (M.op (M.op x X0) (M.op x y)) X0) ∨ (M.op X0 (M.op (M.op x X0) (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq237 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq243 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) = X0 ∨ (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (k (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq54 eq12
    | (have j0 := eq12 (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0
       have r₂ := eq54 X0
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (k (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) ∨ (M.op X0 (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq243 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq333 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq123 eq16
    | exact resolve eq16 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq417 : (k (M.op x y) (k x (M.op x y))) = (τ (k (σ (M.op x y)) (k (σ x) (σ (M.op x y))))) := by
    first
    | exact superpose eq63 eq333
    | exact resolve eq333 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq423 : (k (M.op x y) (k (M.op x y) (M.op x y))) = (τ (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq155 eq333
    | exact resolve eq333 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq595 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq601 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq595 (M.op X0 X1)
       grind)
    | exact superpose eq595 eq52
    | exact resolve eq52 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq605 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq595 X0
       grind)
    | exact superpose eq595 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | exact resolve eq13 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq595 X0
       grind)
    | exact superpose eq595 eq14
    | exact resolve eq14 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq595 (M.op X0 X1)
       grind)
    | exact superpose eq595 eq55
    | exact resolve eq55 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq841 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq910 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq606 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq606
    | exact resolve eq606 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq912 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq53 eq606
    | exact resolve eq606 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq914 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54 eq606
    | exact resolve eq606 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq606
  have eq931 : x ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq912 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq914 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq914
       grind)
    | exact resolve eq12 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq914 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq944
  have eq995 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) = (k (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) ∨ (M.op X1 (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq53 eq72
    | exact resolve eq72 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq72
  have eq1177 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq955 eq13
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq955
       grind)
    | exact resolve eq13 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1190 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq1177
  have eq6865 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq170 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq170
    | (have j0 := eq170 x
       grind)
    | exact resolve eq170 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq6892 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6865
  have eq6897 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6892
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq6892
    | exact resolve eq6892 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq6892
  have eq6914 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6897
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6897 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6897
  have eq6919 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6914 eq49
    | exact resolve eq49 eq6914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq6914
  have eq7239 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq212
    | (have j0 := eq212 (M.op x y)
       grind)
    | exact resolve eq212 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq7264 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq7239
  have eq7267 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq132 eq7264
    | exact resolve eq7264 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq7264
  have eq7298 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq7267
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq7267 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7267
  have eq7336 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq7298 eq155
    | exact resolve eq155 eq7298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq13089 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq13089
    | exact resolve eq13089 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13089
  have eq13101 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq13090
       have r₂ := eq27
       grind)
    | exact resolve eq13090 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13090
  have eq13103 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq13101
    | exact resolve eq13101 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13101
  have eq13117 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13103 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13103
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq13103
       grind)
    | exact resolve eq13 eq13103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13103
  have eq13154 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq13117
  have eq13265 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13154 eq59
    | exact resolve eq59 eq13154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13154
  have eq13288 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq13265
    | exact resolve eq13265 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13265
  have eq14464 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq13288
       grind)
    | exact superpose eq13288 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq13288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13288
  have eq14465 : y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14464
  have eq14469 : y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14465
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14465
    | exact resolve eq14465 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14465
  have eq14470 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14469
  have eq14495 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq14470
       grind)
    | exact superpose eq14470 eq14
    | exact resolve eq14 eq14470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14534 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq910 y x
       have i₂ := eq14470
       grind)
    | exact superpose eq14470 eq910
    | exact resolve eq910 eq14470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14470
  have eq14555 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14495 X0
       have i₂ := eq910 y X0
       grind)
    | exact superpose eq910 eq14495
    | exact resolve eq14495 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14495
  have eq15436 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq14534
       grind)
    | exact superpose eq14534 eq14
    | exact resolve eq14 eq14534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15496 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15436 X0
       have i₂ := eq910 y X0
       grind)
    | exact superpose eq910 eq15436
    | exact resolve eq15436 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15436
  have eq21006 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14555 y
       have i₂ := eq14534
       grind)
    | exact superpose eq14534 eq14555
    | exact resolve eq14555 eq14534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14534 eq14555
  have eq21073 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21006
  have eq21551 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15496 x
       have i₂ := eq21073
       grind)
    | exact superpose eq21073 eq15496
    | exact resolve eq15496 eq21073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15496 eq21073
  have eq21624 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21551
  have eq21627 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21624
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21624
    | exact resolve eq21624 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21624
  have eq21628 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21627
  have eq21629 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21628 eq27
    | exact resolve eq27 eq21628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21671 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21628 eq1190
    | exact resolve eq1190 eq21628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq21965 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op (M.op x (M.op x y)) X0)) ∨ (M.op (M.op x (M.op x y)) X0) = (M.op (M.op (M.op x (M.op x y)) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq995 sF0 (M.op (M.op x sF0) x)
       have i₂ := eq14 sF0 (M.op x sF0) x
       grind)
    | exact superpose eq14 eq995
    | exact resolve eq995 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq21990 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op (M.op x y) X0)) ∨ (M.op (M.op x (M.op x y)) X0) = (M.op (M.op (M.op x (M.op x y)) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq912 eq21965
    | (have j0 := eq21965 X0
       grind)
    | exact resolve eq21965 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21965
  have eq21993 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq912 eq21990
    | (have j0 := eq21990 X0
       grind)
    | exact resolve eq21990 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21990
  have eq23733 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq106 eq21671
    | exact resolve eq21671 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23738 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21671 eq106
    | exact resolve eq106 eq21671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq21671
  have eq23758 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq23738
  have eq23760 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq23733
  have eq23767 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq23758
       have r₂ := eq21629
       grind)
    | exact resolve eq23758 eq21629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23758
  have eq23772 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq23760
       have r₂ := eq21629
       grind)
    | exact resolve eq23760 eq21629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21629 eq23760
  have eq23780 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq23772
       grind)
    | exact superpose eq23772 eq14
    | exact resolve eq14 eq23772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23821 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq910 y x
       have i₂ := eq23772
       grind)
    | exact superpose eq23772 eq910
    | exact resolve eq910 eq23772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23848 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq23780 X0
       have i₂ := eq910 y X0
       grind)
    | exact superpose eq910 eq23780
    | exact resolve eq23780 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23780
  have eq28222 : (τ (σ x)) = (k x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23767 eq59
    | exact resolve eq59 eq23767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq23767
  have eq28266 : x = (k x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq28222
    | exact resolve eq28222 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28222
  have eq28271 : y = (M.op y x) ∨ x = (k x y) := by
    first
    | (have r₁ := eq28266
       have r₂ := eq69
       grind)
    | exact resolve eq28266 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq28266
  have eq28279 : y ≠ y ∨ y = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq28271
       grind)
    | exact superpose eq28271 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq28271
       grind)
    | exact resolve eq13 eq28271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28329 : y = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq910 y x
       have i₂ := eq28271
       grind)
    | exact superpose eq28271 eq910
    | exact resolve eq910 eq28271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28271
  have eq28333 : y = (k x y) ∨ x = (k x y) := by grind
  clear eq28279
  have eq28377 : y ≠ y ∨ y = (k y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq28329
       grind)
    | exact superpose eq28329 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq28329
       grind)
    | exact resolve eq13 eq28329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28329
  have eq28431 : y = (k y y) ∨ x = (k x y) := by grind
  clear eq28377
  have eq29500 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq28333
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq28333
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq28333 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29501 : (σ y) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq28333
       grind)
    | exact superpose eq28333 eq44
    | exact resolve eq44 eq28333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28333
  have eq29523 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq29500
  have eq29540 : (σ y) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq29501
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29501
    | exact resolve eq29501 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29501
  have eq29541 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq29523
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29523
    | exact resolve eq29523 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29523
  have eq29554 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29541
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29541
    | exact resolve eq29541 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29541
  have eq29728 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq841 y y
       have i₂ := eq28431
       grind)
    | exact superpose eq28431 eq841
    | (have j0 := eq841 y y
       grind)
    | exact resolve eq841 eq28431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28431
  have eq29729 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by grind
  clear eq29728
  have eq29730 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by grind
  clear eq29729
  have eq29742 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq29730
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29730
    | exact resolve eq29730 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29730
  have eq29889 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq29742 eq14
    | exact resolve eq14 eq29742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29742
  have eq29968 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq29889 x
       have i₂ := eq910 sF3 x
       grind)
    | exact superpose eq910 eq29889
    | exact resolve eq29889 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29889
  have eq31328 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq601 y x
       have i₂ := eq29554
       grind)
    | exact superpose eq29554 eq601
    | exact resolve eq601 eq29554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq29554
  have eq31378 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31328
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31328
    | exact resolve eq31328 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31328
  have eq32689 : x ≠ x ∨ x = (M.op x (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31378 eq12
    | (have j0 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq31378
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq31378
       grind)
    | exact resolve eq12 eq31378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31378
  have eq32744 : x = (M.op x (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq32689
  have eq32748 : x = (M.op x (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq32744
       have r₂ := eq931
       grind)
    | exact resolve eq32744 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32744
  have eq32752 : x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq912 eq32748
    | exact resolve eq32748 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32748
  have eq32753 : (M.op x y) = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq32752
       have r₂ := eq931
       grind)
    | exact resolve eq32752 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931 eq32752
  have eq32857 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32753 eq130
    | exact resolve eq130 eq32753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq32895 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq32857
    | exact resolve eq32857 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32857
  have eq39985 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23848 y
       have i₂ := eq23821
       grind)
    | exact superpose eq23821 eq23848
    | exact resolve eq23848 eq23821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23821 eq23848
  have eq40079 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq39985
  have eq48127 : y = (M.op (M.op y x) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq667 y x
       have i₂ := eq23772
       grind)
    | exact superpose eq23772 eq667
    | exact resolve eq667 eq23772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq23772
  have eq54004 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq48127
       have i₂ := eq40079
       grind)
    | exact superpose eq40079 eq48127
    | exact resolve eq48127 eq40079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40079 eq48127
  have eq54074 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq54004
  have eq54084 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq54074
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54074
    | exact resolve eq54074 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq54074
  have eq54085 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq54084
  have eq54089 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54085 eq28
    | exact resolve eq28 eq54085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54180 : (k x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54085 eq6919
    | exact resolve eq6919 eq54085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54244 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54085 eq32895
    | exact resolve eq32895 eq54085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32895
  have eq54287 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq54244
  have eq54334 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7298 eq54287
    | exact resolve eq54287 eq7298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54287
  have eq54364 : (k x x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7336 eq54180
    | exact resolve eq54180 eq7336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54180
  have eq54419 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq54089
    | exact resolve eq54089 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54089
  have eq54726 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54419 eq20
    | exact resolve eq20 eq54419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54842 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq54419
  have eq54905 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq54726
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq54726
    | exact resolve eq54726 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54726
  have eq54954 : (k y x) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54905 eq85
    | exact resolve eq85 eq54905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54905
  have eq55185 : (k y x) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq141 eq54954
    | exact resolve eq54954 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54954
  have eq55973 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54334 eq7336
    | exact resolve eq7336 eq54334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54334
  have eq56094 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq55973
    | exact resolve eq55973 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55973
  have eq56495 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54364 eq56094
    | exact resolve eq56094 eq54364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54364 eq56094
  have eq56523 : (M.op x y) = (k x x) ∨ y = (M.op x y) := by grind
  clear eq56495
  have eq56643 : (σ x) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq841 x x
       have i₂ := eq56523
       grind)
    | exact superpose eq56523 eq841
    | (have j0 := eq841 x x
       grind)
    | exact resolve eq841 eq56523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56523
  have eq56649 : (σ x) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq56643
  have eq56672 : (σ x) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq56649
    | exact resolve eq56649 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56649
  have eq56694 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56672
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56672
    | exact resolve eq56672 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56672
  have eq56713 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq56694
       have r₂ := eq54085
       grind)
    | exact resolve eq56694 eq54085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54085 eq56694
  have eq56727 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56713
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56713
    | exact resolve eq56713 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56713
  have eq57068 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56727 eq247
    | exact resolve eq247 eq56727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq56727
  have eq57210 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq914 eq57068
    | exact resolve eq57068 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57068
  have eq57242 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq57210
       have i₂ := eq910 sF2 sF4
       grind)
    | exact superpose eq910 eq57210
    | exact resolve eq57210 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57210
  have eq57245 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq914 eq57242
    | exact resolve eq57242 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57242
  have eq57246 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq57245
       have r₂ := eq945
       grind)
    | exact resolve eq57245 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq57245
  have eq57694 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21628 eq57246
    | exact resolve eq57246 eq21628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21628 eq57246
  have eq57716 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq57694
  have eq57980 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq57716 eq85
    | exact resolve eq85 eq57716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq57716
  have eq58023 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq57980
    | exact resolve eq57980 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq57980
  have eq64908 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55185 eq32753
    | exact resolve eq32753 eq55185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32753 eq55185
  have eq64949 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq64908
       have r₂ := eq65
       grind)
    | exact resolve eq64908 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64908
  have eq65072 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58023
       have i₂ := eq64949
       grind)
    | exact superpose eq64949 eq58023
    | exact resolve eq58023 eq64949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58023 eq64949
  have eq65087 : y = (M.op x y) := by grind
  clear eq65072
  have eq65202 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq65087 eq20
    | exact resolve eq20 eq65087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq65207 : x ≠ y ∨ y = (k y x) := by
    first
    | exact superpose eq65087 eq65
    | exact resolve eq65 eq65087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq65383 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq65202
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq65202
    | exact resolve eq65202 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65202
  have eq65422 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq65383 eq26
    | exact resolve eq26 eq65383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq65551 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x y) := by
    first
    | exact superpose eq65383 eq29540
    | exact resolve eq29540 eq65383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29540
  have eq65554 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq65383 eq29968
    | exact resolve eq29968 eq65383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29968
  have eq65741 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq65422 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq65422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71727 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq65551 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq65551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65551
  have eq71743 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (k x y) := by grind
  clear eq71727
  have eq71748 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq65422 eq71743
    | exact resolve eq71743 eq65422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71743
  have eq71760 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq71748
       have r₂ := eq27
       grind)
    | exact resolve eq71748 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71748
  have eq72174 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ x)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq71760 eq14
    | exact resolve eq14 eq71760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72276 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (σ x)) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq72174 x
       have i₂ := eq910 sF1 x
       grind)
    | exact superpose eq910 eq72174
    | exact resolve eq72174 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72174
  have eq75410 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y X0) y) ∨ (M.op x y) = (k (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq65087 eq21993
    | (have j0 := eq21993 X0
       grind)
    | exact resolve eq21993 eq65087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21993
  have eq75411 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y X0) y) ∨ y = (k y (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq65087 eq75410
    | (have j0 := eq75410 X0
       grind)
    | exact resolve eq75410 eq65087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75410
  have eq75502 : y = (M.op y y) ∨ y = (k y (M.op y y)) := by
    first
    | (have i₁ := eq595 y
       have i₂ := eq75411 y
       grind)
    | exact superpose eq75411 eq595
    | (have j1 := eq75411 y
       grind)
    | exact resolve eq595 eq75411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq75411
  have eq75674 : y = (k y (M.op y y)) := by
    first
    | (have j1 := eq605 y
       grind)
    | (have r₁ := eq75502
       have r₂ := eq605 y
       grind)
    | exact resolve eq75502 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605 eq75502
  have eq79983 : (k (σ y) (σ (M.op x y))) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq65087 eq114
    | exact resolve eq114 eq65087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq79984 : (σ (M.op y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq65383 eq79983
    | exact resolve eq79983 eq65383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79983
  have eq79985 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq7298 eq79984
    | exact resolve eq79984 eq7298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7298 eq79984
  have eq79986 : y = (M.op y y) ∨ (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq65087 eq79985
    | exact resolve eq79985 eq65087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79985
  have eq79987 : y = (M.op y y) ∨ y = (M.op y y) ∨ (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq65087 eq79986
    | exact resolve eq79986 eq65087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79986
  have eq79988 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by grind
  clear eq79987
  have eq79993 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq79988
       grind)
    | exact superpose eq79988 eq16
    | exact resolve eq16 eq79988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79988
  have eq80102 : (M.op y y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7336 eq79993
    | exact resolve eq79993 eq7336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7336 eq79993
  have eq80115 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq65087 eq80102
    | exact resolve eq80102 eq65087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80102
  have eq80128 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq80115
       have r₂ := eq13 y y
       grind)
    | exact resolve eq80115 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80115
  have eq95157 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq71760 eq72276
    | exact resolve eq72276 eq71760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71760 eq72276
  have eq95286 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (k x y) := by grind
  clear eq95157
  have eq96159 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq95286 eq65554
    | exact resolve eq65554 eq95286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65554 eq95286
  have eq96238 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (k x y) := by grind
  clear eq96159
  have eq96250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq65422 eq96238
    | exact resolve eq96238 eq65422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96238
  have eq96253 : x = (k x y) := by
    first
    | (have r₁ := eq96250
       have r₂ := eq27
       grind)
    | exact resolve eq96250 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96250
  have eq96264 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq96253
       grind)
    | exact superpose eq96253 eq44
    | exact resolve eq44 eq96253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq96315 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq65383 eq96264
    | exact resolve eq96264 eq65383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96264
  have eq96338 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq96315
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq96315
    | exact resolve eq96315 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96315
  have eq96484 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq96338 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq96338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96503 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq65422 eq96484
    | exact resolve eq96484 eq65422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96484
  have eq96519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq65422 eq96503
    | exact resolve eq96503 eq65422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96503
  have eq96531 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq96519
       have r₂ := eq27
       grind)
    | exact resolve eq96519 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96519
  have eq97398 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq96531 eq13
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq96531
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq96531
       grind)
    | exact resolve eq13 eq96531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96531
  have eq97474 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq97398
  have eq97518 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq96338 eq97474
    | exact resolve eq97474 eq96338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96338 eq97474
  have eq97575 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq97518 eq914
    | exact resolve eq914 eq97518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq97642 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq97518 eq65741
    | (have r₁ := eq65741
       have r₂ := eq97518
       grind)
    | exact resolve eq65741 eq97518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65741 eq97518
  have eq97664 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq97642
  have eq99971 : (τ (σ x)) = (k x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq97575 eq6919
    | exact resolve eq6919 eq97575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6919 eq97575
  have eq100179 : x = (k x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq99971
    | exact resolve eq99971 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99971
  have eq100222 : (τ (σ x)) = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq97664 eq141
    | exact resolve eq141 eq97664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq97664
  have eq100289 : (τ (σ x)) = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq65087 eq100222
    | exact resolve eq100222 eq65087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100222
  have eq100300 : x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq100289
    | exact resolve eq100289 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100289
  have eq103439 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq100179
       grind)
    | exact superpose eq100179 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq100179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100179
  have eq103463 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq103439
  have eq103740 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) x) ∨ x = (M.op x (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq241 x
       have i₂ := eq103463
       grind)
    | exact superpose eq103463 eq241
    | exact resolve eq241 eq103463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq103463
  have eq103900 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq912 eq103740
    | exact resolve eq103740 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103740
  have eq103936 : y = (k y x) ∨ x = (M.op x (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq65087 eq103900
    | exact resolve eq103900 eq65087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103900
  have eq103948 : x = (M.op x (M.op x y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq103936
       have i₂ := eq910 x sF0
       grind)
    | exact superpose eq910 eq103936
    | exact resolve eq103936 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910 eq103936
  have eq103955 : x = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq912 eq103948
    | exact resolve eq103948 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912 eq103948
  have eq103958 : x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq65087 eq103955
    | exact resolve eq103955 eq65087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103955
  have eq103959 : y = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq103958
       have r₂ := eq65207
       grind)
    | exact resolve eq103958 eq65207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103958
  have eq104101 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq100300
       have i₂ := eq103959
       grind)
    | exact superpose eq103959 eq100300
    | exact resolve eq100300 eq103959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100300 eq103959
  have eq104116 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq104101
  have eq104282 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq104116 eq28
    | exact resolve eq28 eq104116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq104327 : (k (M.op x y) (k x (M.op x y))) = (τ (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y))))) ∨ x = y := by
    first
    | exact superpose eq104116 eq417
    | exact resolve eq417 eq104116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq104116
  have eq104570 : (k (M.op x y) (k x (M.op x y))) = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq423 eq104327
    | exact resolve eq104327 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq104327
  have eq104607 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq104282
    | exact resolve eq104282 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq104282
  have eq104660 : (k y (k x y)) = (k y (k y y)) ∨ x = y := by
    first
    | exact superpose eq65087 eq104570
    | exact resolve eq104570 eq65087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104570
  have eq104694 : x = (M.op x y) := by
    first
    | (have r₁ := eq104607
       have r₂ := eq54842
       grind)
    | exact resolve eq104607 eq54842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54842 eq104607
  have eq104734 : (k y (k x y)) = (k y (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq104660
       have i₂ := eq80128
       grind)
    | exact superpose eq80128 eq104660
    | exact resolve eq104660 eq80128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80128 eq104660
  have eq104764 : x = y := by
    first
    | exact superpose eq65087 eq104694
    | exact resolve eq104694 eq65087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65087 eq104694
  have eq104799 : y = (k y (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq104734
       have i₂ := eq75674
       grind)
    | exact superpose eq75674 eq104734
    | exact resolve eq104734 eq75674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75674 eq104734
  have eq104832 : y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq104799
       have i₂ := eq96253
       grind)
    | exact superpose eq96253 eq104799
    | exact resolve eq104799 eq96253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96253 eq104799
  have eq104844 : y = (k y x) := by
    first
    | (have r₁ := eq104832
       have r₂ := eq65207
       grind)
    | exact resolve eq104832 eq65207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65207 eq104832
  have eq104849 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq104764
       grind)
    | exact superpose eq104764 eq24
    | exact resolve eq24 eq104764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq105200 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq65383 eq104849
    | exact resolve eq104849 eq65383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65383 eq104849
  have eq105299 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq105200
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq105200
    | exact resolve eq105200 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105200
  have eq105658 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq105299 eq65422
    | exact resolve eq65422 eq105299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65422
  have eq106040 : x = (k x x) := by
    first
    | (have i₁ := eq104844
       have i₂ := eq104764
       grind)
    | exact superpose eq104764 eq104844
    | exact resolve eq104844 eq104764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104764 eq104844
  have eq106075 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq841 x x
       have i₂ := eq106040
       grind)
    | exact superpose eq106040 eq841
    | (have j0 := eq841 x x
       grind)
    | exact resolve eq841 eq106040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq106040
  have eq106080 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq106075
  have eq106081 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq106080
  have eq106097 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq106081
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq106081
    | exact resolve eq106081 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq106081
  have eq106119 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq105299 eq106097
    | exact resolve eq106097 eq105299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105299 eq106097
  have eq109833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq106119 eq105658
    | exact resolve eq105658 eq106119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105658 eq106119
  have eq109834 : False := by grind
  exact eq109834
