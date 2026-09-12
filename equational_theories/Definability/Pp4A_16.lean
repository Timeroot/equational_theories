import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq49 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq45 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq224 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq231 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X1
       have j1 := eq49 X1 X0
       grind)
    | (have r₁ := eq224 X0 X0
       have r₂ := eq49 X0 X0
       grind)
    | (have r₁ := eq224 X1 X0
       have r₂ := eq49 X0 X1
       grind)
    | exact resolve eq224 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq224
  have eq444 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq231 (σ X0) (σ X1)
       grind)
    | exact superpose eq231 eq15
    | exact resolve eq15 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq444 X0 X1
       have i₂ := eq231 X0 X1
       grind)
    | exact superpose eq231 eq444
    | exact resolve eq444 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq444
  have eq454 : False := by grind
  exact eq454

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = X then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pyx_pxx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq42 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq77 eq53
    | exact resolve eq53 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op x x) (M.op X0 x)
       have i₂ := eq53 X0 x x
       grind)
    | exact superpose eq53 eq12
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  clear eq18
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq130 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq59
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq59
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq135 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq130
    | exact resolve eq130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq139 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq139
    | exact resolve eq139 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq215 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq10
    | exact resolve eq10 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq28
    | exact resolve eq28 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq223 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq36
    | exact resolve eq36 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq261 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq215 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq215
    | exact resolve eq215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1076 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq10
    | (have j1 := eq121 X0 X1
       grind)
    | exact resolve eq10 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq1103 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1076 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1076
    | (have j0 := eq1076 X0 X1
       grind)
    | exact resolve eq1076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1344 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq218 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq218
    | (have j0 := eq218 x
       grind)
    | exact resolve eq218 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq2029 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq223
    | (have j0 := eq223 (M.op x y)
       grind)
    | exact resolve eq223 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq2080 : (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq2029 eq14
    | (have j0 := eq14 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2081 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq2080
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2080
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2080
    | exact resolve eq2080 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080
  have eq5328 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X0 X1
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq94
    | (have j0 := eq94 X0 X0 X1
       grind)
    | (have r₁ := eq94 x x x
       have r₂ := eq53 x x x
       grind)
    | exact resolve eq94 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq5329 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5328 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5328
  have eq5333 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq83 eq99
    | (have r₁ := eq99 (M.op x y) y
       have r₂ := eq83 (M.op x y)
       grind)
    | exact resolve eq99 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5334 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq80 eq99
    | (have r₁ := eq99 x (M.op x y)
       have r₂ := eq80 x
       grind)
    | exact resolve eq99 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq5340 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq5334
  have eq5341 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq5333
  have eq5346 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5340 eq1344
    | exact resolve eq1344 eq5340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq5348 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5341 eq2081
    | exact resolve eq2081 eq5341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081
  have eq5349 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5341 eq2029
    | exact resolve eq2029 eq5341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029 eq5341
  have eq5350 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq5346
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5346
    | exact resolve eq5346 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5346
  have eq5353 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq5349
    | exact resolve eq5349 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5349
  have eq5354 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq5348
    | exact resolve eq5348 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5348
  have eq28818 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq5340
       have i₂ := eq1103 sF0 (M.op x x)
       grind)
    | exact superpose eq1103 eq5340
    | (have j1 := eq1103 (M.op x y) (M.op x x)
       grind)
    | exact resolve eq5340 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq5340
  have eq29179 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq28818
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq28818
    | exact resolve eq28818 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28818
  have eq29426 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq29179
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29179
    | exact resolve eq29179 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29179
  have eq29566 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | exact superpose eq20 eq29426
    | exact resolve eq29426 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29426
  have eq29668 : (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29566
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq29566
    | exact resolve eq29566 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29566
  have eq29724 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29668
       have i₂ := eq53 (σ x) (σ x) (σ x)
       grind)
    | (have i₁ := eq29668
       have i₂ := eq53 x (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) x
       grind)
    | exact superpose eq53 eq29668
    | exact resolve eq29668 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29668
  have eq29775 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq29724
    | exact resolve eq29724 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29724
  have eq29818 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29775
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29775
    | exact resolve eq29775 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29775
  have eq86452 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29818 eq53
    | exact resolve eq53 eq29818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29818
  have eq87412 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq5354 eq53
    | exact resolve eq53 eq5354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq87412 eq86452
    | exact resolve eq86452 eq87412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87412
  have eq93123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq93106
    | exact resolve eq93106 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93106
  have eq93134 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq93123
       have r₂ := eq27
       grind)
    | exact resolve eq93123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93123
  have eq93140 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq93134 eq78
    | exact resolve eq78 eq93134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq93143 : (σ y) ≠ (σ y) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq93134 eq13
    | (have j0 := eq13 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq93134
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq93134
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       have r₂ := eq93134
       grind)
    | exact resolve eq13 eq93134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93144 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq93134 eq53
    | exact resolve eq53 eq93134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93134
  have eq93155 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq93143
  have eq93160 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq93155
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq93155
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq93155
    | exact resolve eq93155 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93155
  have eq93165 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5353 eq93160
    | exact resolve eq93160 eq5353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93160
  have eq93426 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq93140 eq93144
    | exact resolve eq93144 eq93140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93140 eq93144
  have eq93445 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq93426
  have eq93474 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq93445 eq261
    | exact resolve eq261 eq93445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93445
  have eq93515 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39 eq93474
    | exact resolve eq93474 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93474
  have eq93534 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq93515 eq13
    | (have j0 := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       have r₂ := eq93515
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq93515
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq93515
       grind)
    | exact resolve eq13 eq93515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93515
  have eq93546 : (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq93534
  have eq93551 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq93546
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq93546
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq93546
    | exact resolve eq93546 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93546
  have eq93556 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5350 eq93551
    | exact resolve eq93551 eq5350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93551
  have eq188495 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq93556 eq53
    | exact resolve eq53 eq93556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93556
  have eq427917 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq93165 eq53
    | exact resolve eq53 eq93165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93165
  have eq430983 : ∀ X0 X1 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X1)) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq427917 eq53
    | (have j1 := eq427917 X1
       grind)
    | exact resolve eq53 eq427917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427917
  have eq1197500 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq430983 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430983
  have eq1197501 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1197500 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197500
  have eq1197507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1197501 eq86452
    | exact resolve eq86452 eq1197501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197501
  have eq1197520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1197507
  have eq1197525 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq1197520
    | exact resolve eq1197520 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197520
  have eq1197531 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1197525
       have r₂ := eq27
       grind)
    | exact resolve eq1197525 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197525
  have eq1197630 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1197531 eq53
    | exact resolve eq53 eq1197531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197531
  have eq1198037 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1197630 eq1197630
    | exact resolve eq1197630 eq1197630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1198116 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1198037
  have eq1198134 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1198116 eq5354
    | exact resolve eq5354 eq1198116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5354
  have eq1198283 : (τ (σ (M.op x y))) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1198116 eq261
    | exact resolve eq261 eq1198116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq1198116
  have eq1198481 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1198134
  have eq1198505 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq37 eq1198283
    | exact resolve eq1198283 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198283
  have eq1199266 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1198505 eq83
    | exact resolve eq83 eq1198505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1198505
  have eq1226443 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1198481 eq1197630
    | exact resolve eq1197630 eq1198481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197630
  have eq1226458 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1226443
  have eq1231097 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1226458 eq1198481
    | exact resolve eq1198481 eq1226458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198481 eq1226458
  have eq1231141 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1231097
  have eq1231262 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1231141 eq53
    | exact resolve eq53 eq1231141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1231264 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1231141 eq82
    | exact resolve eq82 eq1231141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231141
  have eq1234256 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1231262 eq188495
    | exact resolve eq188495 eq1231262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188495 eq1231262
  have eq1234378 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1234256
  have eq1234512 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq1234378
    | exact resolve eq1234378 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234378
  have eq1234582 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1234512
       have r₂ := eq27
       grind)
    | exact resolve eq1234512 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234512
  have eq1246610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1234582 eq1231264
    | exact resolve eq1231264 eq1234582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231264 eq1234582
  have eq1246649 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq1246610
  have eq1246700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1246649
    | exact resolve eq1246649 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246649
  have eq1246731 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1246700
       have r₂ := eq27
       grind)
    | exact resolve eq1246700 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246700
  have eq1249640 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq77 y
       have i₂ := eq1246731
       grind)
    | exact superpose eq1246731 eq77
    | exact resolve eq77 eq1246731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246731
  have eq1250259 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1249640 eq1199266
    | exact resolve eq1199266 eq1249640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199266 eq1249640
  have eq1250453 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1250259
  have eq1250474 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1250453 eq39
    | exact resolve eq39 eq1250453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1250453
  have eq1250582 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq1250474
    | exact resolve eq1250474 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1250474
  have eq1250583 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1250582
  have eq1250587 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1250583 eq20
    | exact resolve eq20 eq1250583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1250588 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1250583 eq77
    | exact resolve eq77 eq1250583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1253052 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq1253251 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1250587
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1250587
    | exact resolve eq1250587 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250587
  have eq1253645 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1250588 (M.op y x)
       have i₂ := eq1250588 x
       grind)
    | exact superpose eq1250588 eq1250588
    | exact resolve eq1250588 eq1250588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250588
  have eq1253951 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1253645
  have eq1254932 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq140 y
       have i₂ := eq1253951
       grind)
    | exact superpose eq1253951 eq140
    | exact resolve eq140 eq1253951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253951
  have eq1255340 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1254932
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1254932
    | exact resolve eq1254932 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254932
  have eq1255371 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1253251 eq1255340
    | exact resolve eq1255340 eq1253251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253251 eq1255340
  have eq1255872 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1255371
  have eq1255977 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1255872 eq5353
    | exact resolve eq5353 eq1255872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5353 eq1255872
  have eq1256519 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq1255977
    | exact resolve eq1255977 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255977
  have eq1263441 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1250583 eq1256519
    | exact resolve eq1256519 eq1250583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250583 eq1256519
  have eq1264044 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1263441
       have r₂ := eq1253052
       grind)
    | exact resolve eq1263441 eq1253052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253052 eq1263441
  have eq1264050 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1264044
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq1264044
    | exact resolve eq1264044 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264044
  have eq1264052 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1264050
       have i₂ := eq140 y
       grind)
    | exact superpose eq140 eq1264050
    | exact resolve eq1264050 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264050
  have eq1264054 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1264052
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1264052
    | exact resolve eq1264052 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1264052
  have eq1264624 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1264054 eq82
    | exact resolve eq82 eq1264054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1264627 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1264054 eq5329
    | exact resolve eq5329 eq1264054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264054
  have eq1264909 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1264627
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq1264627
    | exact resolve eq1264627 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264627
  have eq1265332 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1264909 eq86452
    | exact resolve eq86452 eq1264909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86452 eq1264909
  have eq1265749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq1265332
  have eq1265946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1265749
    | exact resolve eq1265749 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265749
  have eq1265964 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1265946
       have r₂ := eq27
       grind)
    | exact resolve eq1265946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265946
  have eq1291320 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1265964 eq13
    | (have j0 := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       have r₂ := eq1265964
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1265964
       grind)
    | exact resolve eq13 eq1265964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265964
  have eq1291335 : (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq1291320
  have eq1291460 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1291335
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq1291335
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq1291335
    | exact resolve eq1291335 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq1291335
  have eq1291467 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5350 eq1291460
    | exact resolve eq1291460 eq5350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5350 eq1291460
  have eq2129963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1291467 eq1264624
    | exact resolve eq1264624 eq1291467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291467
  have eq2129968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2129963
  have eq2129970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq2129968
    | exact resolve eq2129968 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2129968
  have eq2129972 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2129970
       have r₂ := eq27
       grind)
    | exact resolve eq2129970 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2129970
  have eq2130110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2129972 eq1264624
    | exact resolve eq1264624 eq2129972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264624 eq2129972
  have eq2130134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2130110
  have eq2130267 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2130134
    | exact resolve eq2130134 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130134
  have eq2130322 : x = (M.op x y) := by
    first
    | (have r₁ := eq2130267
       have r₂ := eq27
       grind)
    | exact resolve eq2130267 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130267
  have eq2130324 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2130322 eq20
    | exact resolve eq20 eq2130322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2130331 : (k (σ y) (σ (M.op x y))) = (σ (k y x)) := by
    first
    | exact superpose eq2130322 eq42
    | exact resolve eq42 eq2130322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq2130333 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq2130322 eq80
    | exact resolve eq80 eq2130322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq2130336 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq2130322 eq95
    | exact resolve eq95 eq2130322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq2156431 : x = (k y x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq2130322 eq2130336
    | exact resolve eq2130336 eq2130322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130322 eq2130336
  have eq2156434 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2130324
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2130324
    | exact resolve eq2130324 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130324
  have eq2156745 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2156434 eq22
    | exact resolve eq22 eq2156434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq2156746 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2156434 eq26
    | exact resolve eq26 eq2156434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2156758 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2156434 eq135
    | exact resolve eq135 eq2156434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq2162897 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) := by
    first
    | exact superpose eq2156434 eq2156758
    | exact resolve eq2156758 eq2156434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156434 eq2156758
  have eq2165078 : x = (M.op x x) := by
    first
    | (have i₁ := eq2130333 (M.op x x)
       have i₂ := eq2130333 x
       grind)
    | exact superpose eq2130333 eq2130333
    | exact resolve eq2130333 eq2130333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130333
  have eq2165365 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq2156431
       have i₂ := eq2165078
       grind)
    | exact superpose eq2165078 eq2156431
    | (have r₁ := eq2156431
       have r₂ := eq2165078
       grind)
    | exact resolve eq2156431 eq2165078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156431
  have eq2165402 : x = (k y x) := by grind
  clear eq2165365
  have eq2165421 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2130331
       have i₂ := eq2165402
       grind)
    | exact superpose eq2165402 eq2130331
    | exact resolve eq2130331 eq2165402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130331
  have eq2165454 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2162897
       have i₂ := eq2165402
       grind)
    | exact superpose eq2165402 eq2162897
    | exact resolve eq2162897 eq2165402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162897 eq2165402
  have eq2165473 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2165454
       have i₂ := eq2156745
       grind)
    | exact superpose eq2156745 eq2165454
    | exact resolve eq2165454 eq2156745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165454
  have eq2165495 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2165421
       have i₂ := eq2156745
       grind)
    | exact superpose eq2156745 eq2165421
    | exact resolve eq2165421 eq2156745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165421
  have eq2169100 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq140 x
       have i₂ := eq2165078
       grind)
    | exact superpose eq2165078 eq140
    | exact resolve eq140 eq2165078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq2165078
  have eq2169239 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2169100
       have i₂ := eq2156745
       grind)
    | exact superpose eq2156745 eq2169100
    | exact resolve eq2169100 eq2156745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156745 eq2169100
  have eq2169429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2169239 eq2165473
    | exact resolve eq2165473 eq2169239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165473
  have eq2169475 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq2169429
       have r₂ := eq27
       grind)
    | exact resolve eq2169429 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169429
  have eq2172963 : (σ y) ≠ (σ y) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2169475 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq2169475
       grind)
    | exact resolve eq13 eq2169475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169475
  have eq2172983 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2172963
  have eq2172989 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2156746 eq2172983
    | exact resolve eq2172983 eq2156746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172983
  have eq2172993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2169239 eq2172989
    | exact resolve eq2172989 eq2169239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172989
  have eq2172994 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq2172993
       have r₂ := eq27
       grind)
    | exact resolve eq2172993 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172993
  have eq2172995 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2165495 eq2172994
    | exact resolve eq2172994 eq2165495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165495 eq2172994
  have eq2173828 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2172995 eq5329
    | exact resolve eq5329 eq2172995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5329 eq2172995
  have eq2173842 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2173828
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq2173828
    | exact resolve eq2173828 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq2173828
  have eq2173869 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2169239 eq2173842
    | exact resolve eq2173842 eq2169239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173842
  have eq2173870 : (σ (M.op x y)) = (σ y) := by grind
  clear eq2173869
  have eq2177849 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2173870 eq2156746
    | exact resolve eq2156746 eq2173870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156746 eq2173870
  have eq2178215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2169239 eq2177849
    | exact resolve eq2177849 eq2169239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169239 eq2177849
  have eq2178432 : False := by grind
  exact eq2178432

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pyx_pxy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq133 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
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
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq177 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq16 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
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
  have eq190 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq191 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 X0 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq177 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y X0
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y) X0
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X2 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq195 eq177
    | exact resolve eq177 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq200 eq177
    | exact resolve eq177 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq189
       grind)
    | exact superpose eq189 eq40
    | exact resolve eq40 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq585
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq585
    | exact resolve eq585 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq588 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq586
    | exact resolve eq586 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq595 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq191 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq191
    | (have j0 := eq191 (σ X0)
       grind)
    | exact resolve eq191 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq588 eq190
    | exact resolve eq190 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq677
       have r₂ := eq27
       grind)
    | exact resolve eq677 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq689 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq684 eq196
    | exact resolve eq196 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq694 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq684 eq177
    | exact resolve eq177 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq684 eq177
    | exact resolve eq177 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  have eq707 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq177 X0 X0 X0
       grind)
    | exact superpose eq177 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 X1
       have i₂ := eq713 X0
       grind)
    | exact superpose eq713 eq712
    | (have j0 := eq712 X0 X1
       grind)
    | exact resolve eq712 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq719 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq707
       have i₂ := eq713 sF2
       grind)
    | exact superpose eq713 eq707
    | exact resolve eq707 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq722 : (M.op x y) ≠ (k x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq704
       have i₂ := eq713 x
       grind)
    | exact superpose eq713 eq704
    | exact resolve eq704 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq725 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) ≠ X0 ∨ (M.op (k X0 X0) X1) = (k X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq714 X0 X1
       have i₂ := eq713 X0
       grind)
    | exact superpose eq713 eq714
    | (have j0 := eq714 X0 X1
       grind)
    | exact resolve eq714 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq727 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq743 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq684 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq684
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq684
       grind)
    | exact resolve eq12 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq745 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq743
  have eq747 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq745
       have i₂ := eq713 sF2
       grind)
    | exact superpose eq713 eq745
    | exact resolve eq745 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq763 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq727 X0 X1
       have i₂ := eq713 X0
       grind)
    | exact superpose eq713 eq727
    | (have j0 := eq727 X0 X1
       grind)
    | exact resolve eq727 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq764 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq747
    | exact resolve eq747 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq772 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq689 eq177
    | exact resolve eq177 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq689 eq694
    | exact resolve eq694 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq694
  have eq832 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq819
  have eq835 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq832
       have i₂ := eq713 sF3
       grind)
    | exact superpose eq713 eq832
    | exact resolve eq832 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq839 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq835 eq153
    | exact resolve eq153 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq843 : y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq839
    | exact resolve eq839 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq880 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (k (M.op (σ y) X0) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq772 eq13
    | exact resolve eq13 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq895 : ∀ X0 : G, (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k (M.op (σ y) X0) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq880 X0
       have i₂ := eq713 sF3
       grind)
    | exact superpose eq713 eq880
    | (have j0 := eq880 X0
       grind)
    | exact resolve eq880 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq899 : ∀ X0 : G, (σ y) = (k (M.op (σ y) X0) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq895 X0
       grind)
    | (have r₁ := eq895 X0
       have r₂ := eq835
       grind)
    | exact resolve eq895 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835 eq895
  have eq925 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq695 eq899
    | exact resolve eq899 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq899
  have eq930 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq925
  have eq935 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq930 eq91
    | exact resolve eq91 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq938 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq935
    | exact resolve eq935 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq987 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq764 eq98
    | exact resolve eq98 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq994 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq588 eq987
    | exact resolve eq987 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq998 : (k (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq994
       grind)
    | exact superpose eq994 eq40
    | exact resolve eq40 eq994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1001 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq998
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq998
    | exact resolve eq998 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1003 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1001
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1001
    | exact resolve eq1001 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1083 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq713 X0
       grind)
    | exact superpose eq713 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1086 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X1 X0 X0
       have i₂ := eq713 X0
       grind)
    | exact superpose eq713 eq177
    | exact resolve eq177 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1087 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X0 X1
       have i₂ := eq713 X0
       grind)
    | exact superpose eq713 eq177
    | exact resolve eq177 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1099 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0 X0 X0
       have i₂ := eq713 (M.op X0 X0)
       grind)
    | exact superpose eq713 eq177
    | exact resolve eq177 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1112 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1099 X0
       have i₂ := eq713 X0
       grind)
    | exact superpose eq713 eq1099
    | exact resolve eq1099 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1121 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1003 eq719
    | (have r₁ := eq719
       have r₂ := eq1003
       grind)
    | exact resolve eq719 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq1122 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq764 eq719
    | (have r₁ := eq719
       have r₂ := eq764
       grind)
    | exact resolve eq719 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq764
  have eq1123 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq1122
  have eq1124 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq1121
  have eq1125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq588 eq1123
    | exact resolve eq1123 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq588 eq1124
    | exact resolve eq1124 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq1124
  have eq1127 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1125
       have r₂ := eq27
       grind)
    | exact resolve eq1125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1128 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1126
       have r₂ := eq27
       grind)
    | exact resolve eq1126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1130 : y = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq195 x
       have i₂ := eq1128
       grind)
    | exact superpose eq1128 eq195
    | exact resolve eq195 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1131 : x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq200 y
       have i₂ := eq1128
       grind)
    | exact superpose eq1128 eq200
    | exact resolve eq200 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y x
       have i₂ := eq1128
       grind)
    | exact superpose eq1128 eq177
    | exact resolve eq177 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1167 : y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1131 eq195
    | exact resolve eq195 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1172 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1131 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1185 : y ≠ (M.op (M.op x y) (M.op x y)) ∨ y = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1167 eq13
    | exact resolve eq13 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1188 : y = (k x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1167 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | exact resolve eq28 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1195 : y ≠ (k (M.op x y) (M.op x y)) ∨ y = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1185
       have i₂ := eq713 sF0
       grind)
    | exact superpose eq713 eq1185
    | exact resolve eq1185 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1205 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1127 eq142
    | exact resolve eq142 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1210 : y = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq1205
    | exact resolve eq1205 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1213 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq189 eq1210
    | exact resolve eq1210 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq1210
  have eq1218 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq195 x
       have i₂ := eq1213
       grind)
    | exact superpose eq1213 eq195
    | exact resolve eq195 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1219 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq200 y
       have i₂ := eq1213
       grind)
    | exact superpose eq1213 eq200
    | exact resolve eq200 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1220 : y ≠ y ∨ (M.op x y) = (M.op x x) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1213
       grind)
    | exact superpose eq1213 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1213
       grind)
    | exact resolve eq12 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y x
       have i₂ := eq1213
       grind)
    | exact superpose eq1213 eq177
    | exact resolve eq177 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1225 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq177 y x X0
       have i₂ := eq1213
       grind)
    | exact superpose eq1213 eq177
    | exact resolve eq177 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1230 : (M.op x y) = (M.op x x) ∨ y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq1220
  have eq1232 : (M.op x y) = (k x x) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1230
       have i₂ := eq713 x
       grind)
    | exact superpose eq713 eq1230
    | exact resolve eq1230 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1234 : (M.op x y) = (k x x) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1232
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1232
    | exact resolve eq1232 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232
  have eq1243 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1218 eq177
    | exact resolve eq177 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1253 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1219 eq195
    | exact resolve eq195 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1258 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1219 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1288 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1218 eq1224
    | exact resolve eq1224 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1302 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq1288
  have eq1306 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1302
       have i₂ := eq713 y
       grind)
    | exact superpose eq713 eq1302
    | exact resolve eq1302 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302
  have eq1355 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1130 eq1136
    | exact resolve eq1136 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1369 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1355
  have eq1373 : y = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1369
       have i₂ := eq713 y
       grind)
    | exact superpose eq713 eq1369
    | exact resolve eq1369 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1378 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1373
       grind)
    | exact superpose eq1373 eq41
    | exact resolve eq41 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq1382 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1378
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1378
    | exact resolve eq1378 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1428 : ∀ X0 : G, y ≠ (M.op y y) ∨ y = (k (M.op y X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op y X0) y
       have i₂ := eq1243 X0
       grind)
    | exact superpose eq1243 eq13
    | exact resolve eq13 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1443 : ∀ X0 : G, y ≠ (k y y) ∨ y = (k (M.op y X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1428 X0
       have i₂ := eq713 y
       grind)
    | exact superpose eq713 eq1428
    | (have j0 := eq1428 X0
       grind)
    | exact resolve eq1428 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq1449 : ∀ X0 : G, y = (k (M.op y X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1443 X0
       grind)
    | (have r₁ := eq1443 X0
       have r₂ := eq1306
       grind)
    | exact resolve eq1443 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306 eq1443
  have eq1663 : y = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1219 eq1449
    | exact resolve eq1449 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219 eq1449
  have eq1668 : y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq1663
  have eq1675 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq1668
       grind)
    | exact superpose eq1668 eq36
    | exact resolve eq36 eq1668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq1678 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1675
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1675
    | exact resolve eq1675 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1675
  have eq1964 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq722
       have i₂ := eq1234
       grind)
    | exact superpose eq1234 eq722
    | (have r₁ := eq722
       have r₂ := eq1234
       grind)
    | exact resolve eq722 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1969 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1234
       grind)
    | exact superpose eq1234 eq40
    | exact resolve eq40 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1972 : (M.op x y) = (k y x) ∨ y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq1964
  have eq1974 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1969
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1969
    | exact resolve eq1969 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969
  have eq1977 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1974
    | exact resolve eq1974 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974
  have eq2000 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1258 eq1218
    | exact resolve eq1218 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2001 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1258 eq1130
    | exact resolve eq1130 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq2022 : x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2001
  have eq2023 : x = (k (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq2000
  have eq2030 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2023 eq41
    | exact resolve eq41 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2031 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2030
    | exact resolve eq2030 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030
  have eq2033 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2031
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2031
    | exact resolve eq2031 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031
  have eq2050 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1972
       grind)
    | exact superpose eq1972 eq40
    | exact resolve eq40 eq1972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1972
  have eq2052 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2050
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2050
    | exact resolve eq2050 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050
  have eq2054 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2052
    | exact resolve eq2052 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2078 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1172 eq225
    | exact resolve eq225 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2087 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1172 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq2102 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2022 eq2087
    | exact resolve eq2087 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087
  have eq2106 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2022 eq2102
    | exact resolve eq2102 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102
  have eq2110 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq191 (M.op x y)
       grind)
    | (have r₁ := eq2106
       have r₂ := eq191 (M.op x y)
       grind)
    | exact resolve eq2106 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq2106
  have eq2112 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2110
       have i₂ := eq713 sF0
       grind)
    | exact superpose eq713 eq2110
    | exact resolve eq2110 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110
  have eq2328 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2054 eq190
    | exact resolve eq190 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq2054
  have eq2339 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2328
       have r₂ := eq27
       grind)
    | exact resolve eq2328 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328
  have eq2345 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1188 eq42
    | exact resolve eq42 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq2348 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2345
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2345
    | exact resolve eq2345 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345
  have eq2350 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2348
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2348
    | exact resolve eq2348 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348
  have eq2371 : y ≠ (M.op x y) ∨ y = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2112 eq1195
    | exact resolve eq1195 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq2381 : y ≠ (M.op x y) ∨ y = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k (M.op x y) y) := by grind
  clear eq2371
  have eq2386 : y = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k (M.op x y) y) := by
    first
    | (have r₁ := eq2381
       have r₂ := eq2023
       grind)
    | exact resolve eq2381 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2381
  have eq2387 : (M.op x y) = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq2022 eq2386
    | exact resolve eq2386 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2386
  have eq2423 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2339 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2339
       grind)
    | exact resolve eq12 eq2339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339
  have eq2435 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq2423
  have eq2436 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2435
       have i₂ := eq713 sF2
       grind)
    | exact superpose eq713 eq2435
    | exact resolve eq2435 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2435
  have eq2437 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2436
    | exact resolve eq2436 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2436
  have eq2438 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1977 eq2437
    | exact resolve eq2437 eq1977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977 eq2437
  have eq2439 : (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2438
       have r₂ := eq27
       grind)
    | exact resolve eq2438 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2438
  have eq2464 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq2387 eq36
    | exact resolve eq36 eq2387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387
  have eq2472 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq20 eq2464
    | exact resolve eq2464 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2464
  have eq2555 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2439 eq142
    | exact resolve eq142 eq2439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2439
  have eq2561 : y = (k y x) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq2555
    | exact resolve eq2555 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2555
  have eq2562 : y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq2561
  have eq2576 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq2562
       grind)
    | exact superpose eq2562 eq40
    | exact resolve eq40 eq2562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562
  have eq2582 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2576
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2576
    | exact resolve eq2576 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2576
  have eq3227 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq2472 eq2350
    | exact resolve eq2350 eq2472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350 eq2472
  have eq3234 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x (M.op x y)) ∨ x = (k (M.op x y) y) := by grind
  clear eq3227
  have eq3240 : x = (k (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2078 eq3234
    | exact resolve eq3234 eq2078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078 eq3234
  have eq5703 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1086 y X0
       have i₂ := eq843
       grind)
    | exact superpose eq843 eq1086
    | exact resolve eq1086 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5710 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1382 eq1086
    | exact resolve eq1086 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086 eq1382
  have eq5741 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq1224 eq5703
    | (have j0 := eq5703 X0
       have j1 := eq1224 X0
       grind)
    | exact resolve eq5703 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224 eq5703
  have eq5818 : ∀ X0 : G, (M.op X0 y) = (M.op (k (M.op X0 y) (M.op X0 y)) y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1087 (M.op X0 y) y
       have i₂ := eq1136 X0
       grind)
    | exact superpose eq1136 eq1087
    | exact resolve eq1087 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq6198 : ∀ X0 : G, (σ y) = (M.op (k (σ y) X0) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq5710 x
       have i₂ := eq28 sF3 x
       grind)
    | exact superpose eq28 eq5710
    | (have j1 := eq28 (σ y) X0
       grind)
    | exact resolve eq5710 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6640 : y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq5741 (M.op x y)
       have i₂ := eq5741 x
       grind)
    | exact superpose eq5741 eq5741
    | exact resolve eq5741 eq5741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6648 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq5741 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5741
    | (have j0 := eq5741 x
       grind)
    | exact resolve eq5741 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5741
  have eq6683 : y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq6640
  have eq6696 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq6683
       have i₂ := eq713 y
       grind)
    | exact superpose eq713 eq6683
    | exact resolve eq6683 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6683
  have eq6705 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6648 eq225
    | exact resolve eq225 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6706 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6648 eq200
    | exact resolve eq200 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6708 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6648 eq13
    | exact resolve eq13 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6713 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq6648 eq177
    | exact resolve eq177 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6728 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6648 eq1087
    | exact resolve eq1087 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6733 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq6708
       have i₂ := eq713 sF0
       grind)
    | exact superpose eq713 eq6708
    | exact resolve eq6708 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6708
  have eq6735 : y = (M.op (M.op x y) y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq6706
       have i₂ := eq713 sF0
       grind)
    | exact superpose eq713 eq6706
    | exact resolve eq6706 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6706
  have eq6746 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (k y y) := by
    first
    | exact superpose eq6696 eq200
    | exact resolve eq200 eq6696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6696
  have eq6775 : y = (k y y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq6746
       have i₂ := eq713 sF0
       grind)
    | exact superpose eq713 eq6746
    | exact resolve eq6746 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6746
  have eq6782 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6705 eq209
    | exact resolve eq209 eq6705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq6783 : x ≠ (M.op x y) ∨ (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6705 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq6705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6807 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ x ≠ (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq6783
       have i₂ := eq713 sF0
       grind)
    | exact superpose eq713 eq6783
    | exact resolve eq6783 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6783
  have eq6808 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1218 eq6782
    | exact resolve eq6782 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6782
  have eq6810 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x ≠ (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6648 eq6807
    | exact resolve eq6807 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6807
  have eq6811 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq6808
       have i₂ := eq713 sF0
       grind)
    | exact superpose eq713 eq6808
    | exact resolve eq6808 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6808
  have eq6812 : x ≠ (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq6810
       have r₂ := eq6733
       grind)
    | exact resolve eq6810 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6733 eq6810
  have eq6833 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq6735 eq177
    | exact resolve eq177 eq6735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq7273 : (M.op x y) = (M.op x x) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6713 eq225
    | exact resolve eq225 eq6713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7275 : ∀ X0 : G, x ≠ (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x X0) (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq6713 eq13
    | exact resolve eq13 eq6713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6713
  have eq7299 : ∀ X0 : G, x ≠ (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x X0) (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq7275 X0
       have i₂ := eq713 sF0
       grind)
    | exact superpose eq713 eq7275
    | (have j0 := eq7275 X0
       grind)
    | exact resolve eq7275 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7275
  have eq7301 : (M.op x y) = (k x x) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq7273
       have i₂ := eq713 x
       grind)
    | exact superpose eq713 eq7273
    | exact resolve eq7273 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7273
  have eq7307 : ∀ X0 : G, x = (k (M.op x X0) (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have j0 := eq7299 X0
       grind)
    | (have r₁ := eq7299 X0
       have r₂ := eq6735
       grind)
    | exact resolve eq7299 eq6735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7299
  have eq7309 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq722
       have i₂ := eq7301
       grind)
    | exact superpose eq7301 eq722
    | (have r₁ := eq722
       have r₂ := eq7301
       grind)
    | exact resolve eq722 eq7301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq7301
  have eq7323 : (M.op x y) = (k y x) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq7309
  have eq7327 : (M.op x y) = (k (M.op x y) x) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1218 eq7323
    | exact resolve eq7323 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218 eq7323
  have eq7336 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq7327 eq40
    | exact resolve eq40 eq7327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq7327
  have eq7339 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq20 eq7336
    | exact resolve eq7336 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7336
  have eq7341 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1130 eq7339
    | exact resolve eq7339 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7339
  have eq7343 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2582 eq7341
    | exact resolve eq7341 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2582 eq7341
  have eq7345 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7343
       have i₂ := eq713 sF0
       grind)
    | exact superpose eq713 eq7343
    | exact resolve eq7343 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7343
  have eq7609 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7345 eq142
    | exact resolve eq142 eq7345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq7345
  have eq7616 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (k y x) := by
    first
    | exact superpose eq32 eq7609
    | exact resolve eq7609 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7609
  have eq7832 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6728 eq12
    | (have j0 := eq12 (k (M.op x y) (M.op x y)) (M.op x y)
       grind)
    | exact resolve eq12 eq6728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6728
  have eq7859 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq7832
       have r₂ := eq6811
       grind)
    | exact resolve eq7832 eq6811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6811 eq7832
  have eq7866 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq7859
       have i₂ := eq713 sF0
       grind)
    | exact superpose eq713 eq7859
    | exact resolve eq7859 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7859
  have eq7868 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6735 eq7866
    | exact resolve eq7866 eq6735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7866
  have eq7869 : x = (M.op x y) ∨ (M.op x y) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6648 eq7868
    | exact resolve eq7868 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6648 eq7868
  have eq7870 : x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6735 eq7869
    | exact resolve eq7869 eq6735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6735 eq7869
  have eq7871 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq7870
       have r₂ := eq6812
       grind)
    | exact resolve eq7870 eq6812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6812 eq7870
  have eq7876 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq7871 eq36
    | exact resolve eq36 eq7871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq7871
  have eq7884 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq20 eq7876
    | exact resolve eq7876 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7876
  have eq7886 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1130 eq7884
    | exact resolve eq7884 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7884
  have eq7888 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1678 eq7886
    | exact resolve eq7886 eq1678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678 eq7886
  have eq7890 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7888
       have i₂ := eq713 sF0
       grind)
    | exact superpose eq713 eq7888
    | exact resolve eq7888 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7888
  have eq7893 : (τ (σ y)) = (k x (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7890 eq91
    | exact resolve eq91 eq7890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq7890
  have eq7899 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (k x y) := by
    first
    | exact superpose eq32 eq7893
    | exact resolve eq7893 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7893
  have eq8436 : ∀ X0 : G, y ≠ (M.op y y) ∨ y = (k (M.op y X0) y) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op y X0) y
       have i₂ := eq6833 X0
       grind)
    | exact superpose eq6833 eq13
    | exact resolve eq13 eq6833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6833
  have eq8463 : ∀ X0 : G, y ≠ (k y y) ∨ y = (k (M.op y X0) y) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq8436 X0
       have i₂ := eq713 y
       grind)
    | exact superpose eq713 eq8436
    | (have j0 := eq8436 X0
       grind)
    | exact resolve eq8436 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8436
  have eq8482 : ∀ X0 : G, y = (k (M.op y X0) y) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq8463 X0
       grind)
    | (have r₁ := eq8463 X0
       have r₂ := eq6775
       grind)
    | exact resolve eq8463 eq6775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8463
  have eq8629 : ∀ X0 : G, (σ x) = (k (σ (M.op x X0)) (σ (M.op x y))) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq7307 eq42
    | exact resolve eq42 eq7307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7307
  have eq8633 : ∀ X0 : G, (σ x) = (k (σ (M.op x X0)) (σ (M.op x y))) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq8629 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8629
    | (have j0 := eq8629 X0
       grind)
    | exact resolve eq8629 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8629
  have eq8635 : ∀ X0 : G, (σ x) = (k (σ (M.op x X0)) (σ y)) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq1130 eq8633
    | exact resolve eq8633 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq8633
  have eq12901 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6705 eq8635
    | (have j0 := eq8635 y
       grind)
    | exact resolve eq8635 eq6705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6705 eq8635
  have eq12914 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq12901
  have eq12922 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq20 eq12914
    | exact resolve eq12914 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12914
  have eq12933 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2033 eq12922
    | exact resolve eq12922 eq2033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033 eq12922
  have eq12943 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq12933
       have i₂ := eq713 sF0
       grind)
    | exact superpose eq713 eq12933
    | exact resolve eq12933 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12933
  have eq12949 : (τ (σ x)) = (k (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq12943 eq133
    | exact resolve eq133 eq12943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq12943
  have eq12956 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq30 eq12949
    | exact resolve eq12949 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12949
  have eq12969 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ x = (k (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq12956 eq1087
    | exact resolve eq1087 eq12956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13026 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq12969 eq225
    | exact resolve eq225 eq12969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq12969
  have eq20707 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq192 x y X0
       have i₂ := eq938
       grind)
    | exact superpose eq938 eq192
    | (have j0 := eq192 x y x
       grind)
    | exact resolve eq192 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq21117 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op y (M.op x X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq20707 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20707
    | (have j0 := eq20707 X0
       grind)
    | exact resolve eq20707 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20707
  have eq21130 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq1225 eq21117
    | (have j0 := eq21117 X0
       have j1 := eq1225 X0
       grind)
    | exact resolve eq21117 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225 eq21117
  have eq23085 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq195 (M.op x x)
       have i₂ := eq21130 x
       grind)
    | exact superpose eq21130 eq195
    | exact resolve eq195 eq21130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21130
  have eq23289 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op (M.op x y) x) := by grind
  clear eq23085
  have eq23292 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23289
       have r₂ := eq1253
       grind)
    | exact resolve eq23289 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253 eq23289
  have eq23340 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23292 eq200
    | exact resolve eq200 eq23292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq23342 : y ≠ (M.op (M.op x y) (M.op x y)) ∨ y = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23292 eq13
    | exact resolve eq13 eq23292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23292
  have eq23373 : y ≠ (k (M.op x y) (M.op x y)) ∨ y = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23342
       have i₂ := eq713 sF0
       grind)
    | exact superpose eq713 eq23342
    | exact resolve eq23342 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23342
  have eq23418 : y = (k x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23340 eq8482
    | exact resolve eq8482 eq23340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8482
  have eq23456 : y = (M.op (k y y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23340 eq1087
    | exact resolve eq1087 eq23340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq23466 : y = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7899 eq23418
    | exact resolve eq23418 eq7899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7899 eq23418
  have eq23467 : y = (k x y) ∨ x = (M.op x y) := by grind
  clear eq23466
  have eq23485 : y ≠ y ∨ (M.op x y) = (k x x) ∨ y = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq763 x y
       have i₂ := eq23467
       grind)
    | exact superpose eq23467 eq763
    | (have j0 := eq763 x y
       grind)
    | (have r₁ := eq763 x y
       have r₂ := eq23467
       grind)
    | exact resolve eq763 eq23467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq23487 : (M.op x y) = (k x x) ∨ y = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23485
  have eq23490 : (M.op x y) = (k x x) ∨ y = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23487
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23487
    | exact resolve eq23487 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23487
  have eq23495 : x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23490
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23490
    | exact resolve eq23490 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23490
  have eq23496 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq23495
  have eq23864 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq197 x y X0
       have i₂ := eq23467
       grind)
    | exact superpose eq23467 eq197
    | (have j0 := eq197 x y x
       grind)
    | exact resolve eq197 eq23467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq23467
  have eq24053 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op (M.op X0 y) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23864 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23864
    | (have j0 := eq23864 X0
       grind)
    | exact resolve eq23864 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23864
  have eq24054 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq24053 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24053
  have eq24126 : x ≠ (k y y) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1131 eq1083
    | exact resolve eq1083 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq24286 : x ≠ (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2022 eq24126
    | exact resolve eq24126 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022 eq24126
  have eq24305 : x ≠ (M.op x y) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2112 eq24286
    | exact resolve eq24286 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2112 eq24286
  have eq24310 : x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq24305
       have r₂ := eq3240
       grind)
    | exact resolve eq24305 eq3240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3240 eq24305
  have eq24318 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24310 eq41
    | exact resolve eq41 eq24310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq24310
  have eq24327 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq24318
    | exact resolve eq24318 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24318
  have eq24329 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24327
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24327
    | exact resolve eq24327 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24327
  have eq24339 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq24329 eq192
    | (have j0 := eq192 (σ (M.op x y)) (σ y) x
       grind)
    | exact resolve eq192 eq24329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24329
  have eq24540 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq23456
       have i₂ := eq843
       grind)
    | exact superpose eq843 eq23456
    | exact resolve eq23456 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843 eq23456
  have eq24572 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq24540
  have eq24577 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq195 x
       have i₂ := eq24572
       grind)
    | exact superpose eq24572 eq195
    | exact resolve eq195 eq24572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq24572
  have eq24671 : y = (k y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24577 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq24577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq24692 : y ≠ (k (M.op x y) (M.op x y)) ∨ y = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24577 eq1083
    | exact resolve eq1083 eq24577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq24701 : y = (k y (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq23340 eq24671
    | exact resolve eq24671 eq23340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23340 eq24671
  have eq24744 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24577 eq24054
    | exact resolve eq24054 eq24577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24054 eq24577
  have eq24793 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq24744
  have eq24804 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24793
       have i₂ := eq713 y
       grind)
    | exact superpose eq713 eq24793
    | exact resolve eq24793 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24793
  have eq27417 : y ≠ (M.op x y) ∨ y = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq12956 eq23373
    | exact resolve eq23373 eq12956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23373
  have eq27421 : y = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | (have r₁ := eq27417
       have r₂ := eq2023
       grind)
    | exact resolve eq27417 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27417
  have eq27423 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq2023 eq27421
    | exact resolve eq27421 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27421
  have eq27645 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1112 x
       have i₂ := eq23496
       grind)
    | exact superpose eq23496 eq1112
    | exact resolve eq1112 eq23496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23496
  have eq27653 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq7616 eq27645
    | exact resolve eq27645 eq7616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7616 eq27645
  have eq27654 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq27653
  have eq28588 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq27423 eq192
    | (have j0 := eq192 x (M.op x y) x
       grind)
    | exact resolve eq192 eq27423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq27423
  have eq28597 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq13026 eq28588
    | (have j0 := eq28588 X0
       grind)
    | exact resolve eq28588 eq13026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28588
  have eq28598 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    intro X0
    first
    | (have j0 := eq28597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28597
  have eq29311 : y ≠ (M.op x y) ∨ y = (k y (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq12956 eq24692
    | exact resolve eq24692 eq12956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24692
  have eq29316 : y = (k y (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | (have r₁ := eq29311
       have r₂ := eq2023
       grind)
    | exact resolve eq29311 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023 eq29311
  have eq29317 : y = (k y (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq24701 eq29316
    | exact resolve eq29316 eq24701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24701 eq29316
  have eq37870 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq13026 eq28598
    | (have j0 := eq28598 y
       grind)
    | exact resolve eq28598 eq13026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13026 eq28598
  have eq37959 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by grind
  clear eq37870
  have eq37968 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | (have i₁ := eq37959
       have i₂ := eq713 sF0
       grind)
    | exact superpose eq713 eq37959
    | exact resolve eq37959 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37959
  have eq37973 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq12956 eq37968
    | exact resolve eq37968 eq12956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12956 eq37968
  have eq37974 : x = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq37973
  have eq38054 : ∀ X0 : G, (M.op X0 y) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k y (k (M.op X0 y) (M.op X0 y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq725 (M.op X0 y) y
       have i₂ := eq5818 X0
       grind)
    | exact superpose eq5818 eq725
    | (have r₁ := eq725 (M.op X0 y) y
       have r₂ := eq5818 X0
       grind)
    | exact resolve eq725 eq5818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq5818
  have eq38079 : ∀ X0 : G, (M.op X0 y) = (k y (k (M.op X0 y) (M.op X0 y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq38054 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38054
  have eq61014 : (M.op x y) = (k y (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq38079 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq38079
    | (have j0 := eq38079 x
       grind)
    | exact resolve eq38079 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq38079
  have eq61073 : (σ (M.op x y)) = (k (σ y) (σ (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq61014 eq37
    | exact resolve eq37 eq61014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq61014
  have eq61091 : (σ (M.op x y)) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq42 eq61073
    | exact resolve eq61073 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq61073
  have eq61093 : (σ (M.op x y)) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq61091
    | exact resolve eq61091 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61091
  have eq61098 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq61093 eq6198
    | (have j0 := eq6198 (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq6198 eq61093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6198
  have eq61108 : (σ y) = (M.op (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq61098
  have eq61167 : (σ y) ≠ (σ y) ∨ (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq61108 eq12
    | (have j0 := eq12 (σ y) (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | (have r₁ := eq12 (σ y) (k (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq61108
       grind)
    | exact resolve eq12 eq61108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61108
  have eq61229 : (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq61167
  have eq61252 : (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq61229
       have i₂ := eq713 (k sF1 sF1)
       grind)
    | exact superpose eq713 eq61229
    | exact resolve eq61229 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61229
  have eq61279 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq61252
       have i₂ := eq1112 sF1
       grind)
    | exact superpose eq1112 eq61252
    | exact resolve eq61252 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq61252
  have eq61280 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq61093 eq61279
    | exact resolve eq61279 eq61093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61093 eq61279
  have eq61281 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq61280
  have eq61483 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq61281 eq5710
    | exact resolve eq5710 eq61281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5710 eq61281
  have eq61586 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq61483
  have eq61616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq61586 eq24339
    | exact resolve eq24339 eq61586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24339 eq61586
  have eq61732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq61616
  have eq61753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq61732
    | exact resolve eq61732 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61732
  have eq61757 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq61753
       have r₂ := eq27
       grind)
    | exact resolve eq61753 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61753
  have eq61759 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq61757 eq29
    | exact resolve eq29 eq61757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq61846 : y = (M.op x y) := by
    first
    | exact superpose eq61759 eq32
    | exact resolve eq32 eq61759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq61847 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq61759 eq14
    | exact resolve eq14 eq61759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61759
  have eq61910 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq6775
       have i₂ := eq61846
       grind)
    | exact superpose eq61846 eq6775
    | exact resolve eq6775 eq61846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6775
  have eq61956 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24804
       have i₂ := eq61846
       grind)
    | exact superpose eq61846 eq24804
    | exact resolve eq24804 eq61846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24804
  have eq61961 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27654
       have i₂ := eq61846
       grind)
    | exact superpose eq61846 eq27654
    | exact resolve eq27654 eq61846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27654
  have eq61963 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq29317
       have i₂ := eq61846
       grind)
    | exact superpose eq61846 eq29317
    | exact resolve eq29317 eq61846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29317
  have eq61967 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37974
       have i₂ := eq61846
       grind)
    | exact superpose eq61846 eq37974
    | exact resolve eq37974 eq61846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37974 eq61846
  have eq61986 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq61967 eq61963
    | exact resolve eq61963 eq61967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61963 eq61967
  have eq61987 : x = (M.op x y) ∨ x = (k (M.op x y) x) := by grind
  clear eq61986
  have eq62009 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq61956 eq61910
    | exact resolve eq61910 eq61956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61910 eq61956
  have eq62010 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq62009
  have eq62020 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61961 eq61987
    | exact resolve eq61987 eq61961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61961 eq61987
  have eq62021 : x = (M.op x y) := by grind
  clear eq62020
  have eq62034 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq62021
       grind)
    | exact superpose eq62021 eq22
    | exact resolve eq22 eq62021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq62021
  have eq62311 : (σ x) = (σ y) := by
    first
    | exact superpose eq62034 eq61847
    | exact resolve eq61847 eq62034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61847
  have eq62312 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq62034 eq20
    | exact resolve eq20 eq62034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62034
  have eq62466 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq62311 eq26
    | exact resolve eq26 eq62311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq62907 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq62466
       have i₂ := eq713 sF2
       grind)
    | exact superpose eq713 eq62466
    | exact resolve eq62466 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62466
  have eq64854 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq62010 eq38
    | exact resolve eq38 eq62010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq62010
  have eq64879 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq64854
    | exact resolve eq64854 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq64854
  have eq64885 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq61757 eq64879
    | exact resolve eq64879 eq61757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61757 eq64879
  have eq64889 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq62311 eq64885
    | exact resolve eq64885 eq62311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62311 eq64885
  have eq64952 : (σ (σ x)) ≠ (σ (σ x)) ∨ (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) := by
    first
    | exact superpose eq64889 eq595
    | (have j0 := eq595 (σ x)
       grind)
    | exact resolve eq595 eq64889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq64889
  have eq64964 : (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) := by grind
  clear eq64952
  have eq64971 : (σ (σ x)) = (k (σ (σ x)) (σ (σ x))) := by
    first
    | (have i₁ := eq64964
       have i₂ := eq713 (σ sF2)
       grind)
    | exact superpose eq713 eq64964
    | exact resolve eq64964 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq64964
  have eq64981 : (σ (σ x)) = (σ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq64971
       have i₂ := eq10 sF2 sF2
       grind)
    | exact superpose eq10 eq64971
    | exact resolve eq64971 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64971
  have eq64988 : (σ (σ x)) = (σ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq62907 eq64981
    | exact resolve eq64981 eq62907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62907 eq64981
  have eq64992 : (M.op (σ x) (σ y)) = (τ (σ (σ x))) := by
    first
    | exact superpose eq64988 eq15
    | exact resolve eq15 eq64988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64988
  have eq65060 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq64992
       have i₂ := eq15 sF2
       grind)
    | exact superpose eq15 eq64992
    | exact resolve eq64992 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64992
  have eq65089 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq65060 eq27
    | exact resolve eq27 eq65060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq65060
  have eq65257 : False := by grind
  exact eq65257

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = X then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pyx_pxy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
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
  have eq42 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq77 eq53
    | exact resolve eq53 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op x x) (M.op X0 x)
       have i₂ := eq53 X0 x x
       grind)
    | exact superpose eq53 eq12
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  clear eq18
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq130 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq59
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq59
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq135 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq130
    | exact resolve eq130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq139 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq139
    | exact resolve eq139 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq215 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq10
    | exact resolve eq10 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq28
    | exact resolve eq28 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq223 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq36
    | exact resolve eq36 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq261 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq215 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq215
    | exact resolve eq215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1076 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq10
    | (have j1 := eq121 X0 X1
       grind)
    | exact resolve eq10 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq1103 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1076 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1076
    | (have j0 := eq1076 X0 X1
       grind)
    | exact resolve eq1076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1344 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq218 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq218
    | (have j0 := eq218 x
       grind)
    | exact resolve eq218 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1374 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1344 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq14 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1375 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1374
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq1374
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq1374
    | exact resolve eq1374 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq2029 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq223
    | (have j0 := eq223 (M.op x y)
       grind)
    | exact resolve eq223 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq2080 : (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq2029 eq14
    | (have j0 := eq14 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2081 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq2080
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2080
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2080
    | exact resolve eq2080 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080
  have eq5328 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X0 X1
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq94
    | (have j0 := eq94 X0 X0 X1
       grind)
    | (have r₁ := eq94 x x x
       have r₂ := eq53 x x x
       grind)
    | exact resolve eq94 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq5329 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5328 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5328
  have eq5333 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq83 eq99
    | (have r₁ := eq99 (M.op x y) y
       have r₂ := eq83 (M.op x y)
       grind)
    | exact resolve eq99 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq5334 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq80 eq99
    | (have r₁ := eq99 x (M.op x y)
       have r₂ := eq80 x
       grind)
    | exact resolve eq99 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq5340 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq5334
  have eq5341 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq5333
  have eq5345 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5340 eq1375
    | exact resolve eq1375 eq5340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq5346 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5340 eq1344
    | exact resolve eq1344 eq5340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq5348 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5341 eq2081
    | exact resolve eq2081 eq5341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081
  have eq5349 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5341 eq2029
    | exact resolve eq2029 eq5341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029 eq5341
  have eq5350 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq5346
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5346
    | exact resolve eq5346 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5346
  have eq5351 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq5345
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5345
    | exact resolve eq5345 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5345
  have eq5353 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq5349
    | exact resolve eq5349 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5349
  have eq5354 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq5348
    | exact resolve eq5348 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5348
  have eq28818 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq5340
       have i₂ := eq1103 sF0 (M.op x x)
       grind)
    | exact superpose eq1103 eq5340
    | (have j1 := eq1103 (M.op x y) (M.op x x)
       grind)
    | exact resolve eq5340 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq5340
  have eq29179 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq28818
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq28818
    | exact resolve eq28818 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28818
  have eq29426 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq29179
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29179
    | exact resolve eq29179 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29179
  have eq29566 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | exact superpose eq20 eq29426
    | exact resolve eq29426 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29426
  have eq29668 : (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29566
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq29566
    | exact resolve eq29566 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29566
  have eq29724 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29668
       have i₂ := eq53 (σ x) (σ x) (σ x)
       grind)
    | (have i₁ := eq29668
       have i₂ := eq53 x (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) x
       grind)
    | exact superpose eq53 eq29668
    | exact resolve eq29668 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29668
  have eq29775 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq29724
    | exact resolve eq29724 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29724
  have eq29818 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29775
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29775
    | exact resolve eq29775 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29775
  have eq79946 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29818 eq53
    | exact resolve eq53 eq29818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29818
  have eq80200 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq5351 eq53
    | exact resolve eq53 eq5351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5351
  have eq80220 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq5354 eq53
    | exact resolve eq53 eq5354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5354
  have eq84372 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq80220 eq78
    | (have j1 := eq80220 X0
       grind)
    | exact resolve eq78 eq80220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq84407 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq84372 eq80200
    | exact resolve eq80200 eq84372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84372
  have eq84442 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq84407
    | exact resolve eq84407 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84407
  have eq84446 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq84442
       have r₂ := eq27
       grind)
    | exact resolve eq84442 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84442
  have eq84471 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq84446 eq53
    | exact resolve eq53 eq84446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84446
  have eq88190 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq84471 eq84471
    | exact resolve eq84471 eq84471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84471
  have eq88232 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq88190
  have eq88267 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq88232 eq261
    | exact resolve eq261 eq88232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq88232
  have eq88318 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39 eq88267
    | exact resolve eq88267 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88267
  have eq88344 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq88318 eq13
    | (have j0 := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       have r₂ := eq88318
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq88318
       grind)
    | exact resolve eq13 eq88318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88345 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq88318 eq53
    | exact resolve eq53 eq88318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88318
  have eq88359 : (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq88344
  have eq88368 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq88359
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq88359
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq88359
    | exact resolve eq88359 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88359
  have eq88375 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5350 eq88368
    | exact resolve eq88368 eq5350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88368
  have eq88376 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq88375
  have eq88454 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq88345 eq88345
    | exact resolve eq88345 eq88345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88487 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq88454
  have eq89698 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq88376 eq53
    | exact resolve eq53 eq88376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88376
  have eq89807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq80220 eq89698
    | exact resolve eq89698 eq80220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89698
  have eq89838 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by grind
  clear eq89807
  have eq89844 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq26 eq89838
    | exact resolve eq89838 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89838
  have eq89848 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq89844
       have r₂ := eq27
       grind)
    | exact resolve eq89844 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89844
  have eq89963 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq88487 eq89848
    | exact resolve eq89848 eq88487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88487 eq89848
  have eq89997 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq89963
  have eq90849 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq89997 eq88345
    | exact resolve eq88345 eq89997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88345
  have eq90868 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq90849
  have eq90885 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq90868 eq89997
    | exact resolve eq89997 eq90868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89997 eq90868
  have eq90918 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq90885
  have eq90940 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq140 y
       have i₂ := eq90918
       grind)
    | exact superpose eq90918 eq140
    | exact resolve eq140 eq90918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90918
  have eq90989 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq90940
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq90940
    | exact resolve eq90940 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90940
  have eq91079 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq90989 eq54
    | exact resolve eq54 eq90989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq91080 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq90989 eq82
    | exact resolve eq82 eq90989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90989
  have eq91347 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq91079 eq80220
    | exact resolve eq80220 eq91079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80220 eq91079
  have eq91377 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq91347
  have eq109029 : (σ y) ≠ (σ y) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq91377 eq13
    | (have j0 := eq13 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq91377
       grind)
    | exact resolve eq13 eq91377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91377
  have eq109044 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq109029
  have eq109071 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq109044
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq109044
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq109044
    | exact resolve eq109044 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109044
  have eq109086 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5353 eq109071
    | exact resolve eq109071 eq5353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109071
  have eq109087 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq109086
  have eq119506 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq109087 eq91080
    | exact resolve eq91080 eq109087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91080 eq109087
  have eq119520 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq119506
  have eq119534 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq119520 eq80200
    | exact resolve eq80200 eq119520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80200
  have eq119551 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq119520 eq53
    | exact resolve eq53 eq119520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq119534
  have eq119585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq119578
    | exact resolve eq119578 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119578
  have eq119591 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq119585
       have r₂ := eq27
       grind)
    | exact resolve eq119585 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119585
  have eq119757 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq119591 eq53
    | exact resolve eq53 eq119591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119591
  have eq119897 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq119757 eq119551
    | exact resolve eq119551 eq119757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119551 eq119757
  have eq119917 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq119897
  have eq119942 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq119917 eq119520
    | exact resolve eq119520 eq119917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119520 eq119917
  have eq119992 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq119942
  have eq120172 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq119992 eq39
    | exact resolve eq39 eq119992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq119992
  have eq120238 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq120172
    | exact resolve eq120172 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120172
  have eq120246 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120238 eq38
    | exact resolve eq38 eq120238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120238
  have eq120328 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq120246
    | exact resolve eq120246 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120246
  have eq120334 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq120328 eq20
    | exact resolve eq20 eq120328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120335 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq120328 eq77
    | exact resolve eq77 eq120328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq120458 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq120482 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120334
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq120334
    | exact resolve eq120334 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120334
  have eq121125 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120335 (M.op y x)
       have i₂ := eq120335 x
       grind)
    | exact superpose eq120335 eq120335
    | exact resolve eq120335 eq120335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120335
  have eq121169 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq121125
  have eq121279 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq140 y
       have i₂ := eq121169
       grind)
    | exact superpose eq121169 eq140
    | exact resolve eq140 eq121169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121169
  have eq121330 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121279
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq121279
    | exact resolve eq121279 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121279
  have eq121341 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq120482 eq121330
    | exact resolve eq121330 eq120482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120482 eq121330
  have eq121426 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq121341
  have eq121495 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq121426 eq5353
    | exact resolve eq5353 eq121426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5353 eq121426
  have eq121582 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq121495
    | exact resolve eq121495 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121495
  have eq121833 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq120328 eq121582
    | exact resolve eq121582 eq120328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120328 eq121582
  have eq121941 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq121833
       have r₂ := eq120458
       grind)
    | exact resolve eq121833 eq120458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120458 eq121833
  have eq121946 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121941
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq121941
    | exact resolve eq121941 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121941
  have eq121949 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121946
       have i₂ := eq140 y
       grind)
    | exact superpose eq140 eq121946
    | exact resolve eq121946 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121946
  have eq121951 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121949
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq121949
    | exact resolve eq121949 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq121949
  have eq122036 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq121951 eq82
    | exact resolve eq82 eq121951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq122041 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq121951 eq5329
    | exact resolve eq5329 eq121951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5329 eq121951
  have eq122070 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq122041
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq122041
    | exact resolve eq122041 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq122041
  have eq122294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122070 eq79946
    | exact resolve eq79946 eq122070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79946 eq122070
  have eq122347 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq122294
  have eq122371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq122347
    | exact resolve eq122347 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122347
  have eq122389 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122371
       have r₂ := eq27
       grind)
    | exact resolve eq122371 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122371
  have eq125926 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122389 eq13
    | (have j0 := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       have r₂ := eq122389
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq122389
       grind)
    | exact resolve eq13 eq122389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122389
  have eq125941 : (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq125926
  have eq125955 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq125941
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq125941
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq125941
    | exact resolve eq125941 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq125941
  have eq125962 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5350 eq125955
    | exact resolve eq125955 eq5350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5350 eq125955
  have eq256795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125962 eq122036
    | exact resolve eq122036 eq125962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122036 eq125962
  have eq256806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq256795
  have eq256814 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq256806
    | exact resolve eq256806 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256806
  have eq256819 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq256814
       have r₂ := eq27
       grind)
    | exact resolve eq256814 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256814
  have eq256824 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq256819 eq38
    | exact resolve eq38 eq256819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq256819
  have eq256954 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq256824
    | exact resolve eq256824 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq256824
  have eq256955 : x = (M.op x y) := by grind
  clear eq256954
  have eq256964 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq256955 eq20
    | exact resolve eq20 eq256955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq256971 : (k (σ y) (σ (M.op x y))) = (σ (k y x)) := by
    first
    | exact superpose eq256955 eq42
    | exact resolve eq42 eq256955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq256973 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq256955 eq80
    | exact resolve eq80 eq256955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq256976 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq256955 eq95
    | exact resolve eq95 eq256955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq280184 : x = (k y x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq256955 eq256976
    | exact resolve eq256976 eq256955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256955 eq256976
  have eq280188 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq256964
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq256964
    | exact resolve eq256964 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256964
  have eq281093 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq280188 eq22
    | exact resolve eq22 eq280188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq281094 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq280188 eq26
    | exact resolve eq26 eq280188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq281106 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq280188 eq135
    | exact resolve eq135 eq280188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq286931 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) := by
    first
    | exact superpose eq280188 eq281106
    | exact resolve eq281106 eq280188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280188 eq281106
  have eq288285 : x = (M.op x x) := by
    first
    | (have i₁ := eq256973 (M.op x x)
       have i₂ := eq256973 x
       grind)
    | exact superpose eq256973 eq256973
    | exact resolve eq256973 eq256973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256973
  have eq288504 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq280184
       have i₂ := eq288285
       grind)
    | exact superpose eq288285 eq280184
    | (have r₁ := eq280184
       have r₂ := eq288285
       grind)
    | exact resolve eq280184 eq288285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280184
  have eq288557 : x = (k y x) := by grind
  clear eq288504
  have eq288588 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq256971
       have i₂ := eq288557
       grind)
    | exact superpose eq288557 eq256971
    | exact resolve eq256971 eq288557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256971
  have eq288617 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq286931
       have i₂ := eq288557
       grind)
    | exact superpose eq288557 eq286931
    | exact resolve eq286931 eq288557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286931 eq288557
  have eq288641 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq288617
       have i₂ := eq281093
       grind)
    | exact superpose eq281093 eq288617
    | exact resolve eq288617 eq281093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288617
  have eq288662 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq288588
       have i₂ := eq281093
       grind)
    | exact superpose eq281093 eq288588
    | exact resolve eq288588 eq281093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288588
  have eq288834 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq140 x
       have i₂ := eq288285
       grind)
    | exact superpose eq288285 eq140
    | exact resolve eq140 eq288285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq288285
  have eq288953 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq288834
       have i₂ := eq281093
       grind)
    | exact superpose eq281093 eq288834
    | exact resolve eq288834 eq281093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281093 eq288834
  have eq289198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq288953 eq288641
    | exact resolve eq288641 eq288953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288641
  have eq289238 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq289198
       have r₂ := eq27
       grind)
    | exact resolve eq289198 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289198
  have eq291061 : (σ y) ≠ (σ y) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq289238 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq289238
       grind)
    | exact resolve eq13 eq289238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289238
  have eq291075 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq291061
  have eq291081 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq281094 eq291075
    | exact resolve eq291075 eq281094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291075
  have eq291085 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq288953 eq291081
    | exact resolve eq291081 eq288953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291081
  have eq291086 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq291085
       have r₂ := eq27
       grind)
    | exact resolve eq291085 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291085
  have eq291087 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq288662 eq291086
    | exact resolve eq291086 eq288662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288662 eq291086
  have eq291088 : (σ (M.op x y)) = (σ y) := by grind
  clear eq291087
  have eq294642 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq291088 eq281094
    | exact resolve eq281094 eq291088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281094 eq291088
  have eq294781 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq288953 eq294642
    | exact resolve eq294642 eq288953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288953 eq294642
  have eq295285 : False := by grind
  exact eq295285

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if m(X,Y) = X then m(Y,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pyy_pyx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
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
  have eq42 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq77 eq53
    | exact resolve eq53 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (k X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op x x)
       have i₂ := eq53 x x x
       grind)
    | exact superpose eq53 eq12
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq130 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq59
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq59
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq135 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq130
    | exact resolve eq130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq139 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq139
    | exact resolve eq139 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq215 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq10
    | exact resolve eq10 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq28
    | exact resolve eq28 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq223 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq36
    | exact resolve eq36 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq261 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq215 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq215
    | exact resolve eq215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq746 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 (M.op X0 X1)
       have i₂ := eq53 X0 X0 X1
       grind)
    | exact superpose eq53 eq99
    | (have j0 := eq99 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq99 x (M.op x x)
       have r₂ := eq53 x x x
       grind)
    | exact resolve eq99 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq83 eq99
    | (have j0 := eq99 (M.op x y) y
       grind)
    | (have r₁ := eq99 (M.op x y) y
       have r₂ := eq83 (M.op x y)
       grind)
    | exact resolve eq99 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq748 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq80 eq99
    | (have j0 := eq99 x (M.op x y)
       grind)
    | (have r₁ := eq99 x (M.op x y)
       have r₂ := eq80 x
       grind)
    | exact resolve eq99 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq754 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq748
  have eq755 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq747
  have eq756 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq746 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq1368 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | exact superpose eq755 eq121
    | (have j0 := eq121 y (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq121 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1370 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq754 eq121
    | (have j0 := eq121 (M.op x y) (M.op x x)
       grind)
    | exact resolve eq121 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1418 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq10
    | (have j1 := eq121 X0 X1
       grind)
    | exact resolve eq10 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq1447 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1418 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1418
    | (have j0 := eq1418 X0 X1
       grind)
    | exact resolve eq1418 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1472 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1370
    | exact resolve eq1370 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1474 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | exact superpose eq20 eq1368
    | exact resolve eq1368 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368
  have eq1511 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1472
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1472
    | exact resolve eq1472 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq1513 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq1474
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1474
    | exact resolve eq1474 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq1533 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1511
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq1511
    | exact resolve eq1511 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq1535 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq1513
       have i₂ := eq140 sF0
       grind)
    | exact superpose eq140 eq1513
    | exact resolve eq1513 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq1547 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1533
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1533
    | exact resolve eq1533 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq1549 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | exact superpose eq20 eq1535
    | exact resolve eq1535 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1559 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1547
    | exact resolve eq1547 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547
  have eq1561 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq1549
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1549
    | exact resolve eq1549 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq1571 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq1559
    | exact resolve eq1559 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559
  have eq1573 : (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1561
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1561
    | exact resolve eq1561 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq1583 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1571
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq1571
    | exact resolve eq1571 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571
  have eq1585 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1573
       have i₂ := eq140 sF0
       grind)
    | exact superpose eq140 eq1573
    | exact resolve eq1573 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq1594 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1583
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1583
    | exact resolve eq1583 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq1596 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq1585
    | exact resolve eq1585 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585
  have eq1605 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1594
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq1594
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq1594
    | exact resolve eq1594 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1607 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1596
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq1596
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq1596
    | exact resolve eq1596 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1725 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq218 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq218
    | (have j0 := eq218 x
       grind)
    | exact resolve eq218 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1736 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq754 eq1725
    | exact resolve eq1725 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725
  have eq1750 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1736
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1736
    | exact resolve eq1736 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq2422 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq223
    | (have j0 := eq223 (M.op x y)
       grind)
    | exact resolve eq223 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq2431 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq755 eq2422
    | exact resolve eq2422 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422
  have eq2445 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq2431
    | exact resolve eq2431 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2431
  have eq38622 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq754
       have i₂ := eq1447 sF0 (M.op x x)
       grind)
    | exact superpose eq1447 eq754
    | (have j1 := eq1447 (M.op x y) (M.op x x)
       grind)
    | exact resolve eq754 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754 eq1447
  have eq39106 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq38622
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq38622
    | exact resolve eq38622 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38622
  have eq39405 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq39106
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39106
    | exact resolve eq39106 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39106
  have eq39571 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq39405
    | exact resolve eq39405 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39405
  have eq39673 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq39571
    | exact resolve eq39571 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39571
  have eq39729 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39673
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq39673
    | exact resolve eq39673 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39673
  have eq39780 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39729
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39729
    | exact resolve eq39729 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39729
  have eq39823 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39780
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq39780
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq39780
    | exact resolve eq39780 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39780
  have eq73081 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1605 eq53
    | exact resolve eq53 eq1605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605
  have eq74421 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq39823 eq53
    | exact resolve eq53 eq39823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39823
  have eq74812 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1607 eq53
    | exact resolve eq53 eq1607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq78709 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq74812 eq78
    | (have j1 := eq74812 X0
       grind)
    | exact resolve eq78 eq74812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq78745 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq78709 eq73081
    | exact resolve eq73081 eq78709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78709
  have eq78777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq78745
    | exact resolve eq78745 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78745
  have eq78781 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq78777
       have r₂ := eq27
       grind)
    | exact resolve eq78777 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78777
  have eq78787 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq78781 eq53
    | exact resolve eq53 eq78781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78781
  have eq78820 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq78787 eq78787
    | exact resolve eq78787 eq78787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78787
  have eq78843 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq78820
  have eq78869 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq78843 eq261
    | exact resolve eq261 eq78843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq78843
  have eq78910 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39 eq78869
    | exact resolve eq78869 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78869
  have eq78929 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq78910 eq13
    | (have j0 := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       have r₂ := eq78910
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq78910
       grind)
    | exact resolve eq13 eq78910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78930 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq78910 eq53
    | exact resolve eq53 eq78910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78910
  have eq78941 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq78929
  have eq78946 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq78941
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq78941
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq78941
    | exact resolve eq78941 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78941
  have eq78951 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1750 eq78946
    | exact resolve eq78946 eq1750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78946
  have eq78952 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq78951
  have eq79025 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq78930 eq78930
    | exact resolve eq78930 eq78930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79049 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq79025
  have eq79751 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq78952 eq53
    | exact resolve eq53 eq78952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78952
  have eq80016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq74812 eq79751
    | exact resolve eq79751 eq74812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79751
  have eq80039 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by grind
  clear eq80016
  have eq80045 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq26 eq80039
    | exact resolve eq80039 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80039
  have eq80049 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq80045
       have r₂ := eq27
       grind)
    | exact resolve eq80045 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80045
  have eq80141 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq79049 eq80049
    | exact resolve eq80049 eq79049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79049 eq80049
  have eq80162 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq80141
  have eq80179 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq80162 eq78930
    | exact resolve eq78930 eq80162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78930
  have eq80193 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq80179
  have eq80206 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq80193 eq80162
    | exact resolve eq80162 eq80193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80162 eq80193
  have eq80226 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq80206
  have eq80241 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq140 y
       have i₂ := eq80226
       grind)
    | exact superpose eq80226 eq140
    | exact resolve eq140 eq80226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80226
  have eq80280 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq80241
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq80241
    | exact resolve eq80241 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80241
  have eq80342 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq80280 eq54
    | exact resolve eq54 eq80280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq80343 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq80280 eq82
    | exact resolve eq82 eq80280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80280
  have eq80702 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq80342 eq74812
    | exact resolve eq74812 eq80342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74812 eq80342
  have eq80722 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq80702
  have eq97304 : (σ y) ≠ (σ y) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq80722 eq13
    | (have j0 := eq13 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq80722
       grind)
    | exact resolve eq13 eq80722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80722
  have eq97319 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq97304
  have eq97341 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq97319
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq97319
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq97319
    | exact resolve eq97319 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97319
  have eq97354 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2445 eq97341
    | exact resolve eq97341 eq2445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97341
  have eq97355 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq97354
  have eq107355 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq97355 eq80343
    | exact resolve eq80343 eq97355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80343 eq97355
  have eq107370 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq107355
  have eq107381 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq107370 eq73081
    | exact resolve eq73081 eq107370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73081
  have eq107394 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq107370 eq53
    | exact resolve eq53 eq107370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq107381
  have eq107424 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq107416
    | exact resolve eq107416 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107416
  have eq107430 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq107424
       have r₂ := eq27
       grind)
    | exact resolve eq107424 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107424
  have eq107797 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq107430 eq53
    | exact resolve eq53 eq107430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107430
  have eq107929 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq107797 eq107394
    | exact resolve eq107394 eq107797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107394 eq107797
  have eq107947 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq107929
  have eq107970 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq107947 eq107370
    | exact resolve eq107370 eq107947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107370 eq107947
  have eq108010 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq107970
  have eq108025 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq108010 eq39
    | exact resolve eq39 eq108010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq108010
  have eq108089 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq108025
    | exact resolve eq108025 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108025
  have eq108097 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq108089 eq38
    | exact resolve eq38 eq108089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq108089
  have eq108165 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq108097
    | exact resolve eq108097 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq108097
  have eq108169 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108165 eq20
    | exact resolve eq20 eq108165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108170 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq108165 eq77
    | exact resolve eq77 eq108165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq108268 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq108275 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108169
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq108169
    | exact resolve eq108169 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108169
  have eq108895 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108170 (M.op y x)
       have i₂ := eq108170 x
       grind)
    | exact superpose eq108170 eq108170
    | exact resolve eq108170 eq108170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108170
  have eq108934 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq108895
  have eq109026 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq140 y
       have i₂ := eq108934
       grind)
    | exact superpose eq108934 eq140
    | exact resolve eq140 eq108934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108934
  have eq109070 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109026
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq109026
    | exact resolve eq109026 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109026
  have eq109081 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108275 eq109070
    | exact resolve eq109070 eq108275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108275 eq109070
  have eq109154 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq109081
  have eq109219 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq109154 eq2445
    | exact resolve eq2445 eq109154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2445 eq109154
  have eq109302 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq109219
    | exact resolve eq109219 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109219
  have eq109678 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq108165 eq109302
    | exact resolve eq109302 eq108165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108165 eq109302
  have eq109784 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq109678
       have r₂ := eq108268
       grind)
    | exact resolve eq109678 eq108268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108268 eq109678
  have eq109789 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109784
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq109784
    | exact resolve eq109784 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109784
  have eq109792 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109789
       have i₂ := eq140 y
       grind)
    | exact superpose eq140 eq109789
    | exact resolve eq109789 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109789
  have eq109794 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109792
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq109792
    | exact resolve eq109792 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq109792
  have eq109869 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq109794 eq82
    | exact resolve eq82 eq109794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq109874 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq109794 eq756
    | exact resolve eq756 eq109794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq109794
  have eq109893 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109874
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq109874
    | exact resolve eq109874 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq109874
  have eq109979 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq109893 eq74421
    | exact resolve eq74421 eq109893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74421 eq109893
  have eq110023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq109979
  have eq110044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq110023
    | exact resolve eq110023 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110023
  have eq110062 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq110044
       have r₂ := eq27
       grind)
    | exact resolve eq110044 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110044
  have eq113347 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq110062 eq13
    | (have j0 := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       have r₂ := eq110062
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq110062
       grind)
    | exact resolve eq13 eq110062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110062
  have eq113362 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq113347
  have eq113372 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113362
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq113362
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq113362
    | exact resolve eq113362 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq113362
  have eq113379 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1750 eq113372
    | exact resolve eq113372 eq1750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750 eq113372
  have eq113380 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq113379
  have eq114021 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq113380 eq109869
    | exact resolve eq109869 eq113380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109869 eq113380
  have eq114035 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq114021
  have eq114041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq114035
    | exact resolve eq114035 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114035
  have eq114046 : x = (M.op x y) := by
    first
    | (have r₁ := eq114041
       have r₂ := eq27
       grind)
    | exact resolve eq114041 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114041
  have eq114048 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq114046 eq20
    | exact resolve eq20 eq114046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq114055 : (k (σ y) (σ (M.op x y))) = (σ (k y x)) := by
    first
    | exact superpose eq114046 eq42
    | exact resolve eq42 eq114046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq114057 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq114046 eq80
    | exact resolve eq80 eq114046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq114119 : x = (k y (M.op x x)) := by
    first
    | exact superpose eq114046 eq755
    | exact resolve eq755 eq114046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755 eq114046
  have eq128366 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq114048
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq114048
    | exact resolve eq114048 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114048
  have eq128541 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq128366 eq22
    | exact resolve eq22 eq128366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq128542 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq128366 eq26
    | exact resolve eq26 eq128366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq128554 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq128366 eq135
    | exact resolve eq135 eq128366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq133041 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) := by
    first
    | exact superpose eq128366 eq128554
    | exact resolve eq128554 eq128366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128366 eq128554
  have eq133665 : x = (M.op x x) := by
    first
    | (have i₁ := eq114057 (M.op x x)
       have i₂ := eq114057 x
       grind)
    | exact superpose eq114057 eq114057
    | exact resolve eq114057 eq114057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114057
  have eq133788 : x = (k y x) := by
    first
    | (have i₁ := eq114119
       have i₂ := eq133665
       grind)
    | exact superpose eq133665 eq114119
    | exact resolve eq114119 eq133665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114119
  have eq133951 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq114055
       have i₂ := eq133788
       grind)
    | exact superpose eq133788 eq114055
    | exact resolve eq114055 eq133788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114055
  have eq133980 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq133041
       have i₂ := eq133788
       grind)
    | exact superpose eq133788 eq133041
    | exact resolve eq133041 eq133788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133041 eq133788
  have eq134001 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq133980
       have i₂ := eq128541
       grind)
    | exact superpose eq128541 eq133980
    | exact resolve eq133980 eq128541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133980
  have eq134022 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq133951
       have i₂ := eq128541
       grind)
    | exact superpose eq128541 eq133951
    | exact resolve eq133951 eq128541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133951
  have eq134066 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq140 x
       have i₂ := eq133665
       grind)
    | exact superpose eq133665 eq140
    | exact resolve eq140 eq133665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq133665
  have eq134171 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq134066
       have i₂ := eq128541
       grind)
    | exact superpose eq128541 eq134066
    | exact resolve eq134066 eq128541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128541 eq134066
  have eq134410 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq134171 eq134001
    | exact resolve eq134001 eq134171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134001
  have eq134447 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq134410
       have r₂ := eq27
       grind)
    | exact resolve eq134410 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134410
  have eq136075 : (σ y) ≠ (σ y) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq134447 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq134447
       grind)
    | exact resolve eq13 eq134447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134447
  have eq136089 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq136075
  have eq136095 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq128542 eq136089
    | exact resolve eq136089 eq128542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136089
  have eq136099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq134171 eq136095
    | exact resolve eq136095 eq134171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136095
  have eq136100 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq136099
       have r₂ := eq27
       grind)
    | exact resolve eq136099 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136099
  have eq136101 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq128542 eq136100
    | exact resolve eq136100 eq128542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136100
  have eq136102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq134022 eq136101
    | exact resolve eq136101 eq134022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134022 eq136101
  have eq136103 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq136102
       have r₂ := eq27
       grind)
    | exact resolve eq136102 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136102
  have eq139266 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq136103 eq128542
    | exact resolve eq128542 eq136103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128542 eq136103
  have eq139372 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq134171 eq139266
    | exact resolve eq139266 eq134171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134171 eq139266
  have eq139830 : False := by grind
  exact eq139830

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_x_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
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
  have eq177 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq16 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq16 X0 x x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X0) (k X0 X1)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X2 X3 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (M.op x y) = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq177 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y X0
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y) X0
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq177 X2 X0 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 X0 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq195 eq177
    | exact resolve eq177 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq200 eq177
    | exact resolve eq177 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X1
    first
    | exact superpose eq201 eq177
    | exact resolve eq177 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq189
       grind)
    | exact superpose eq189 eq41
    | exact resolve eq41 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq189
  have eq586 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq585
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq585
    | exact resolve eq585 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq588 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq586
    | exact resolve eq586 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq677 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq588 eq190
    | exact resolve eq190 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq588
  have eq684 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq677
       have r₂ := eq27
       grind)
    | exact resolve eq677 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq689 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq684 eq196
    | exact resolve eq196 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq690 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq684 eq201
    | exact resolve eq201 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq684 eq177
    | exact resolve eq177 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq708
       have i₂ := eq714 sF2
       grind)
    | exact superpose eq714 eq708
    | exact resolve eq708 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq793 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq689 eq177
    | exact resolve eq177 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq690 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq13 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq815 : (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq805
       have i₂ := eq714 sF2
       grind)
    | exact superpose eq714 eq805
    | exact resolve eq805 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq817 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq689 eq815
    | exact resolve eq815 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq815
  have eq860 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq690 eq695
    | exact resolve eq695 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq874 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq860
  have eq878 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq874
       have i₂ := eq714 sF2
       grind)
    | exact superpose eq714 eq874
    | exact resolve eq874 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq883 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq878 eq142
    | exact resolve eq142 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq883
    | exact resolve eq883 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq908 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ (σ x) = (k (σ y) (M.op (σ x) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq793 eq28
    | (have j0 := eq28 (σ y) (M.op (σ x) X0)
       grind)
    | exact resolve eq28 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq991 : (σ x) ≠ (σ x) ∨ (σ y) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq878 eq817
    | (have r₁ := eq817
       have r₂ := eq878
       grind)
    | exact resolve eq817 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq992 : (σ x) ≠ (σ x) ∨ (σ y) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq991
  have eq993 : (σ y) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq992
  have eq994 : (τ (σ y)) = (k (τ (M.op (σ x) (σ y))) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq993 eq142
    | exact resolve eq142 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq993
  have eq995 : y = (k (τ (M.op (σ x) (σ y))) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq32 eq994
    | exact resolve eq994 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq994
  have eq1103 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq714 X0
       grind)
    | exact superpose eq714 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1106 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X1 X0 X0
       have i₂ := eq714 X0
       grind)
    | exact superpose eq714 eq177
    | exact resolve eq177 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1107 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X0 X1
       have i₂ := eq714 X0
       grind)
    | exact superpose eq714 eq177
    | exact resolve eq177 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1119 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0 X0 X0
       have i₂ := eq714 (M.op X0 X0)
       grind)
    | exact superpose eq714 eq177
    | exact resolve eq177 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1129 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1119 X0
       have i₂ := eq714 X0
       grind)
    | exact superpose eq714 eq1119
    | exact resolve eq1119 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1823 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq878 eq720
    | exact resolve eq720 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq878
  have eq1824 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq684 eq1823
    | exact resolve eq1823 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq1823
  have eq2200 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (k (σ y) (M.op (σ x) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq908 eq178
    | (have j1 := eq908 X0
       grind)
    | exact resolve eq178 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq2234 : ∀ X0 : G, (σ x) = (k (σ y) (M.op (σ x) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq2200
    | (have j0 := eq2200 X0
       grind)
    | exact resolve eq2200 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200
  have eq2468 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq690 eq2234
    | exact resolve eq2234 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq2234
  have eq2474 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq2468
  have eq2481 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq2474
       have r₂ := eq1824
       grind)
    | exact resolve eq2474 eq1824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824 eq2474
  have eq2486 : (τ (σ x)) = (k y (τ (σ x))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2481 eq108
    | exact resolve eq108 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq2481
  have eq2493 : x = (k y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq2486
    | exact resolve eq2486 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2486
  have eq2498 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X1) y) x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq185 y x X0 X1
       have i₂ := eq2493
       grind)
    | exact superpose eq2493 eq185
    | (have j0 := eq185 y x x x
       grind)
    | exact resolve eq185 eq2493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2493
  have eq2499 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X1) y) x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq2498 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2498
    | (have j0 := eq2498 X0 X1
       grind)
    | exact resolve eq2498 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2498
  have eq2576 : ∀ X2 : G, x = (M.op y (M.op x X2)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X2
    first
    | (have i₁ := eq177 (M.op (M.op x x) y) x X2
       have i₂ := eq2499 x x
       grind)
    | exact superpose eq2499 eq177
    | exact resolve eq177 eq2499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2499
  have eq2743 : x = (M.op y (k x x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2576 x
       have i₂ := eq714 x
       grind)
    | exact superpose eq714 eq2576
    | exact resolve eq2576 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2576
  have eq2764 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq887 eq2743
    | exact resolve eq2743 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2743
  have eq2765 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq2764
  have eq2768 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq195 x
       have i₂ := eq2765
       grind)
    | exact superpose eq2765 eq195
    | exact resolve eq195 eq2765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2769 : x = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq200 y
       have i₂ := eq2765
       grind)
    | exact superpose eq2765 eq200
    | exact resolve eq200 eq2765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2774 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y x
       have i₂ := eq2765
       grind)
    | exact superpose eq2765 eq177
    | exact resolve eq177 eq2765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2791 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2768 eq200
    | exact resolve eq200 eq2768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2796 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2768 eq28
    | (have j0 := eq28 (M.op x y) x
       grind)
    | exact resolve eq28 eq2768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768
  have eq2818 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2769 eq177
    | exact resolve eq177 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769
  have eq2843 : y = (M.op (M.op x y) y) ∨ x = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2791 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq2791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2791
  have eq3090 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2796 eq209
    | exact resolve eq209 eq2796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq2796
  have eq3443 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2843 eq2774
    | exact resolve eq2774 eq2843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2774
  have eq3465 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by grind
  clear eq3443
  have eq3471 : x = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2765 eq3465
    | exact resolve eq3465 eq2765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765 eq3465
  have eq3497 : y = (M.op x y) ∨ x = (k y (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3090 eq2843
    | exact resolve eq2843 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2843 eq3090
  have eq3523 : y = (M.op x y) ∨ x = (k y (M.op x y)) ∨ y = (k (M.op x y) x) := by grind
  clear eq3497
  have eq3526 : x = (k (M.op x y) x) ∨ x = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3471 eq3523
    | exact resolve eq3523 eq3471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3471 eq3523
  have eq5789 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1106 x X0
       have i₂ := eq887
       grind)
    | exact superpose eq887 eq1106
    | exact resolve eq1106 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq5837 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq2818 eq5789
    | (have j0 := eq5789 X0
       have j1 := eq2818 X0
       grind)
    | exact resolve eq5789 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818 eq5789
  have eq6305 : x = (M.op (M.op x y) x) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq200 (M.op x x)
       have i₂ := eq5837 x
       grind)
    | exact superpose eq5837 eq200
    | exact resolve eq200 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5837
  have eq6352 : x = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq6305 eq200
    | exact resolve eq200 eq6305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6305
  have eq6377 : x = (M.op x (M.op x y)) := by grind
  clear eq6352
  have eq6391 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq6377 eq177
    | exact resolve eq177 eq6377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6393 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq6377 eq178
    | exact resolve eq178 eq6377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6377
  have eq6413 : ∀ X0 : G, x = (M.op (k X0 x) x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6391 X0
       have i₂ := eq28 X0 x
       grind)
    | exact superpose eq28 eq6391
    | (have j1 := eq28 x (k X0 x)
       grind)
    | exact resolve eq6391 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6422 : x = (M.op x x) := by
    first
    | (have i₁ := eq6391 (M.op x x)
       have i₂ := eq6391 x
       grind)
    | exact superpose eq6391 eq6391
    | exact resolve eq6391 eq6391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6481 : x = (k x x) := by
    first
    | (have i₁ := eq6422
       have i₂ := eq714 x
       grind)
    | exact superpose eq714 eq6422
    | exact resolve eq6422 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6422
  have eq6489 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq6481
       grind)
    | exact superpose eq6481 eq40
    | exact resolve eq40 eq6481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6502 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6489
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6489
    | exact resolve eq6489 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6489
  have eq6515 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq6502 eq1106
    | exact resolve eq1106 eq6502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq6551 : ∀ X0 : G, x ≠ (M.op x x) ∨ (M.op (M.op x X0) x) = (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op x X0) x
       have i₂ := eq6393 X0
       grind)
    | exact superpose eq6393 eq13
    | (have j0 := eq13 (M.op x X0) x
       grind)
    | exact resolve eq13 eq6393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6393
  have eq6574 : ∀ X0 : G, x ≠ (k x x) ∨ (M.op (M.op x X0) x) = (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq6551 X0
       have i₂ := eq714 x
       grind)
    | exact superpose eq714 eq6551
    | (have j0 := eq6551 X0
       grind)
    | exact resolve eq6551 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6551
  have eq6583 : ∀ X0 : G, (M.op (M.op x X0) x) = (k (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6574 X0
       grind)
    | (have r₁ := eq6574 X0
       have r₂ := eq6481
       grind)
    | exact resolve eq6574 eq6481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6574
  have eq6707 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6515 eq201
    | exact resolve eq201 eq6515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq6713 : ∀ X1 : G, (σ x) = (M.op (σ x) (M.op (σ x) X1)) := by
    intro X1
    first
    | exact superpose eq6515 eq177
    | exact resolve eq177 eq6515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6760 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq6707 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq13 eq6707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6707
  have eq6782 : (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq6760
       have i₂ := eq714 sF2
       grind)
    | exact superpose eq714 eq6760
    | exact resolve eq6760 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6760
  have eq6788 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have r₁ := eq6782
       have r₂ := eq6502
       grind)
    | exact resolve eq6782 eq6502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6782
  have eq6818 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) X0) (σ x)) = (k (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq6713 eq13
    | (have j0 := eq13 (M.op (σ x) X0) (σ x)
       grind)
    | exact resolve eq13 eq6713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6713
  have eq6840 : ∀ X0 : G, (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op (M.op (σ x) X0) (σ x)) = (k (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq6818 X0
       have i₂ := eq714 sF2
       grind)
    | exact superpose eq714 eq6818
    | (have j0 := eq6818 X0
       grind)
    | exact resolve eq6818 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6818
  have eq6856 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (k (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq6840 X0
       grind)
    | (have r₁ := eq6840 X0
       have r₂ := eq6502
       grind)
    | exact resolve eq6840 eq6502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6840
  have eq6862 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq6788 eq233
    | exact resolve eq233 eq6788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq6788
  have eq7504 : (k (M.op x y) x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq6583 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6583
    | (have j0 := eq6583 y
       grind)
    | exact resolve eq6583 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7525 : ∀ X0 : G, (M.op x X0) = (M.op x (k (M.op x X0) x)) := by
    intro X0
    first
    | (have i₁ := eq178 x X0 x
       have i₂ := eq6583 X0
       grind)
    | exact superpose eq6583 eq178
    | exact resolve eq178 eq6583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7527 : ∀ X0 : G, x = (M.op (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq6391 (M.op x X0)
       have i₂ := eq6583 X0
       grind)
    | exact superpose eq6583 eq6391
    | exact resolve eq6391 eq6583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6391
  have eq7578 : (M.op x y) = (M.op x (k (M.op x y) x)) := by
    first
    | exact superpose eq7504 eq225
    | exact resolve eq225 eq7504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq7603 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) x)) := by
    first
    | exact superpose eq7504 eq1107
    | exact resolve eq1107 eq7504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq7614 : (M.op x y) = (M.op x x) ∨ x = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3526 eq7578
    | exact resolve eq7578 eq3526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526 eq7578
  have eq7650 : (M.op x y) = (k x x) ∨ x = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7614
       have i₂ := eq714 x
       grind)
    | exact superpose eq714 eq7614
    | exact resolve eq7614 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7614
  have eq7653 : x = (k y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7650
       have i₂ := eq6481
       grind)
    | exact superpose eq6481 eq7650
    | exact resolve eq7650 eq6481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7650
  have eq7953 : ∀ X0 : G, x = (k (k (M.op x X0) x) x) ∨ (k (M.op x X0) x) = (M.op x (k (M.op x X0) x)) := by
    intro X0
    first
    | (have i₁ := eq28 (k (M.op x X0) x) x
       have i₂ := eq7527 X0
       grind)
    | exact superpose eq7527 eq28
    | (have j0 := eq28 (k (M.op x X0) x) x
       grind)
    | exact resolve eq28 eq7527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7973 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) x) ∨ x = (k (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq7953 X0
       have i₂ := eq7525 X0
       grind)
    | exact superpose eq7525 eq7953
    | (have j0 := eq7953 X0
       grind)
    | exact resolve eq7953 eq7525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7953
  have eq8136 : (M.op x y) ≠ (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (M.op (k (M.op x y) x) (k (M.op x y) (M.op x y))) = (k (k (M.op x y) x) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq7603 eq13
    | (have j0 := eq13 (k (M.op x y) x) (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq13 eq7603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7603
  have eq8161 : (M.op x y) ≠ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (M.op (k (M.op x y) x) (k (M.op x y) (M.op x y))) = (k (k (M.op x y) x) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq8136
       have i₂ := eq714 (k sF0 sF0)
       grind)
    | exact superpose eq714 eq8136
    | exact resolve eq8136 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8136
  have eq8166 : (M.op (k (M.op x y) x) (k (M.op x y) (M.op x y))) = (k (k (M.op x y) x) (k (M.op x y) (M.op x y))) := by
    first
    | (have r₁ := eq8161
       have r₂ := eq1129 (M.op x y)
       grind)
    | exact resolve eq8161 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129 eq8161
  have eq8330 : ∀ X0 : G, (M.op X0 x) = (k (M.op x (M.op X0 x)) x) := by
    intro X0
    first
    | (have i₁ := eq6583 (M.op X0 x)
       have i₂ := eq199 x x X0
       grind)
    | exact superpose eq199 eq6583
    | exact resolve eq6583 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6583
  have eq8693 : ∀ X0 : G, (M.op x X0) ≠ (k (M.op x X0) x) ∨ (M.op x X0) = (M.op x x) ∨ (M.op x x) = (k (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq12 (k (M.op x X0) x) x
       have i₂ := eq7525 X0
       grind)
    | exact superpose eq7525 eq12
    | (have j0 := eq12 X0 x
       grind)
    | exact resolve eq12 eq7525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8694 : ∀ X0 : G, (M.op x X0) ≠ (M.op x x) ∨ (M.op (k (M.op x X0) x) x) = (k (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq13 (k (M.op x X0) x) x
       have i₂ := eq7525 X0
       grind)
    | exact superpose eq7525 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 (k (M.op x x) x) x
       have r₂ := eq7525 x
       grind)
    | exact resolve eq13 eq7525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7525
  have eq8718 : ∀ X0 : G, (k x x) ≠ (M.op x X0) ∨ (M.op (k (M.op x X0) x) x) = (k (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq8694 X0
       have i₂ := eq714 x
       grind)
    | exact superpose eq714 eq8694
    | (have j0 := eq8694 X0
       grind)
    | exact resolve eq8694 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8694
  have eq8719 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ (M.op x X0) ≠ (k (M.op x X0) x) ∨ (M.op x x) = (k (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq8693 X0
       have i₂ := eq714 x
       grind)
    | exact superpose eq714 eq8693
    | (have j0 := eq8693 X0
       grind)
    | exact resolve eq8693 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8693
  have eq8722 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op (k (M.op x X0) x) x) = (k (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq8718 X0
       have i₂ := eq6481
       grind)
    | exact superpose eq6481 eq8718
    | (have j0 := eq8718 X0
       grind)
    | exact resolve eq8718 eq6481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8718
  have eq8723 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x X0) ≠ (k (M.op x X0) x) ∨ (M.op x x) = (k (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq8719 X0
       have i₂ := eq6481
       grind)
    | exact superpose eq6481 eq8719
    | (have j0 := eq8719 X0
       grind)
    | exact resolve eq8719 eq6481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8719
  have eq8724 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (k (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq8722 X0
       have i₂ := eq7527 X0
       grind)
    | exact superpose eq7527 eq8722
    | (have j0 := eq8722 X0
       grind)
    | exact resolve eq8722 eq7527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8722
  have eq8725 : ∀ X0 : G, (k x x) = (k (k (M.op x X0) x) x) ∨ x = (M.op x X0) ∨ (M.op x X0) ≠ (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq8723 X0
       have i₂ := eq714 x
       grind)
    | exact superpose eq714 eq8723
    | (have j0 := eq8723 X0
       grind)
    | exact resolve eq8723 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8723
  have eq8726 : ∀ X0 : G, x = (k (k (M.op x X0) x) x) ∨ x = (M.op x X0) ∨ (M.op x X0) ≠ (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq8725 X0
       have i₂ := eq6481
       grind)
    | exact superpose eq6481 eq8725
    | (have j0 := eq8725 X0
       grind)
    | exact resolve eq8725 eq6481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8725
  have eq8727 : ∀ X0 : G, x = (k (k (M.op x X0) x) x) ∨ (M.op x X0) ≠ (k (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq8726 X0
       have j1 := eq8724 X0
       grind)
    | (have r₁ := eq8726 X0
       have r₂ := eq8724 X0
       grind)
    | exact resolve eq8726 eq8724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8724 eq8726
  have eq8728 : ∀ X0 : G, x = (k (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have j0 := eq8727 X0
       have j1 := eq7973 X0
       grind)
    | (have r₁ := eq8727 X0
       have r₂ := eq7973 X0
       grind)
    | exact resolve eq8727 eq7973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7973 eq8727
  have eq8918 : ∀ X0 : G, x = (k (M.op X0 x) x) := by
    intro X0
    first
    | (have i₁ := eq8728 (M.op X0 x)
       have i₂ := eq8330 X0
       grind)
    | exact superpose eq8330 eq8728
    | exact resolve eq8728 eq8330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8330 eq8728
  have eq8971 : ∀ X0 : G, (σ x) = (k (σ (M.op X0 x)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 (M.op X0 x)
       have i₂ := eq8918 X0
       grind)
    | exact superpose eq8918 eq40
    | exact resolve eq40 eq8918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8918
  have eq8975 : ∀ X0 : G, (σ x) = (k (σ (M.op X0 x)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq8971 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8971
    | (have j0 := eq8971 X0
       grind)
    | exact resolve eq8971 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8971
  have eq9231 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (k (M.op (σ x) X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq6856 eq178
    | exact resolve eq178 eq6856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq6856
  have eq11275 : x = (M.op y x) ∨ (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq995 eq6413
    | (have j0 := eq6413 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq6413 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6413
  have eq11343 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op y x) := by grind
  clear eq11275
  have eq11457 : x = (M.op (k (τ (M.op (σ x) (σ y))) x) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq11343 eq7527
    | exact resolve eq7527 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7527 eq11343
  have eq11504 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq995 eq11457
    | exact resolve eq11457 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995 eq11457
  have eq11505 : x = (M.op y x) := by grind
  clear eq11504
  have eq11516 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq195 x
       have i₂ := eq11505
       grind)
    | exact superpose eq11505 eq195
    | exact resolve eq195 eq11505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq11528 : ∀ X0 : G, y = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y x
       have i₂ := eq11505
       grind)
    | exact superpose eq11505 eq177
    | exact resolve eq177 eq11505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11565 : y = (k (M.op x y) x) := by
    first
    | exact superpose eq11516 eq7504
    | exact resolve eq7504 eq11516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7504
  have eq11569 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq11516 eq200
    | exact resolve eq200 eq11516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq11575 : (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq11516 eq8975
    | exact resolve eq8975 eq11516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8975 eq11516
  have eq11609 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11575
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11575
    | exact resolve eq11575 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11575
  have eq11627 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq11565 eq40
    | exact resolve eq40 eq11565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq11632 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq11627
    | exact resolve eq11627 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11627
  have eq11634 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq11632
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11632
    | exact resolve eq11632 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11632
  have eq11645 : y = (M.op (M.op x y) y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq11569 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq11569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11690 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 X1) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq11609 eq185
    | (have j0 := eq185 (σ y) (σ x) x x
       grind)
    | exact resolve eq185 eq11609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq11692 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 X1) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq11690
    | (have j0 := eq11690 X0 X1
       grind)
    | exact resolve eq11690 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11690
  have eq12002 : y = (M.op y x) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq11645 eq11528
    | exact resolve eq11528 eq11645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11528
  have eq12010 : y = (k (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq11645 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq11645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq12039 : x = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq11569 eq12010
    | exact resolve eq12010 eq11569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12010
  have eq12044 : x = (k y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq12002
       have i₂ := eq11505
       grind)
    | exact superpose eq11505 eq12002
    | exact resolve eq12002 eq11505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12002
  have eq12046 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq7653 eq12039
    | exact resolve eq12039 eq7653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7653 eq12039
  have eq13265 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11692 eq6515
    | exact resolve eq6515 eq11692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6515
  have eq13285 : ∀ X2 : G, (σ y) = (M.op (M.op X2 (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq11692 eq199
    | exact resolve eq199 eq11692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq11692
  have eq20790 : (M.op y (k (M.op x y) (M.op x y))) = (k y (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq11565 eq8166
    | exact resolve eq8166 eq11565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20791 : (M.op (k (M.op x y) x) (M.op x y)) = (k (k (M.op x y) x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq12046 eq8166
    | exact resolve eq8166 eq12046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12046
  have eq20800 : ∀ X0 : G, (k (M.op x y) x) = (M.op (M.op X0 (k (M.op x y) x)) (k (k (M.op x y) x) (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq8166 eq177
    | exact resolve eq177 eq8166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8166
  have eq20836 : ∀ X0 : G, y = (M.op (M.op X0 y) (k y (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq11565 eq20800
    | exact resolve eq20800 eq11565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20800
  have eq20840 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq11565 eq20791
    | exact resolve eq20791 eq11565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11565 eq20791
  have eq20847 : x = (k y (M.op x y)) ∨ x = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq11569 eq20840
    | exact resolve eq20840 eq11569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20840
  have eq20848 : x = (k y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq20847
  have eq20993 : y = (M.op y (k y (k (M.op x y) (M.op x y)))) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq11645 eq20836
    | exact resolve eq20836 eq11645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11645 eq20836
  have eq21040 : x = (M.op x (k x (k (M.op x y) (M.op x y)))) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq12044 eq20993
    | exact resolve eq20993 eq12044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12044 eq20993
  have eq21047 : (M.op x y) = (M.op (M.op x y) (k (M.op x y) (k (M.op x y) (M.op x y)))) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq20848 eq21040
    | exact resolve eq21040 eq20848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20848 eq21040
  have eq22319 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ x = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21047 eq177
    | exact resolve eq177 eq21047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq21047
  have eq22359 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq22319 eq22319
    | exact resolve eq22319 eq22319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22319
  have eq22422 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) := by grind
  clear eq22359
  have eq22437 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq22422
       have i₂ := eq714 sF0
       grind)
    | exact superpose eq714 eq22422
    | exact resolve eq22422 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22422
  have eq22491 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq22437 eq20790
    | exact resolve eq20790 eq22437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20790 eq22437
  have eq22527 : x = (k y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq11569 eq22491
    | exact resolve eq22491 eq11569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11569 eq22491
  have eq22528 : x = (k y (M.op x y)) := by grind
  clear eq22527
  have eq22544 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq22528 eq42
    | exact resolve eq42 eq22528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq22528
  have eq22549 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq22544
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22544
    | exact resolve eq22544 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq22544
  have eq22551 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq22549
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22549
    | exact resolve eq22549 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22549
  have eq22559 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq22551 eq192
    | (have j0 := eq192 (σ y) (σ (M.op x y)) x
       grind)
    | exact resolve eq192 eq22551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq22551
  have eq23046 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ x))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq22559 eq9231
    | exact resolve eq9231 eq22559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9231 eq22559
  have eq23102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11634 eq23046
    | exact resolve eq23046 eq11634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11634 eq23046
  have eq23116 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq23102
    | exact resolve eq23102 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23102
  have eq23124 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq23116
       have r₂ := eq27
       grind)
    | exact resolve eq23116 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23116
  have eq23142 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23124 eq13285
    | exact resolve eq13285 eq23124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13285 eq23124
  have eq23178 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13265 eq23142
    | exact resolve eq23142 eq13265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13265 eq23142
  have eq23234 : (σ y) = (M.op (σ x) (k (σ y) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23178 eq6862
    | exact resolve eq6862 eq23178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6862 eq23178
  have eq23332 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq11609 eq23234
    | exact resolve eq23234 eq11609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11609 eq23234
  have eq23358 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23332
       have i₂ := eq714 sF2
       grind)
    | exact superpose eq714 eq23332
    | exact resolve eq23332 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23332
  have eq23368 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6502 eq23358
    | exact resolve eq23358 eq6502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23358
  have eq23369 : (σ x) = (σ y) := by grind
  clear eq23368
  have eq23372 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23369 eq26
    | exact resolve eq26 eq23369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq23376 : ∀ X0 : G, (k y X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | exact superpose eq23369 eq48
    | exact resolve eq48 eq23369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq23379 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq23369 eq73
    | exact resolve eq73 eq23369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq23369
  have eq23494 : ∀ X0 : G, (k X0 x) = (k X0 y) := by
    intro X0
    first
    | exact superpose eq60 eq23379
    | exact resolve eq23379 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq23379
  have eq23497 : ∀ X0 : G, (k x X0) = (k y X0) := by
    intro X0
    first
    | exact superpose eq45 eq23376
    | exact resolve eq23376 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq23376
  have eq23501 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq23372
       have i₂ := eq714 sF2
       grind)
    | exact superpose eq714 eq23372
    | exact resolve eq23372 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq23372
  have eq23516 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6502 eq23501
    | exact resolve eq23501 eq6502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6502 eq23501
  have eq23658 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq23516 eq27
    | exact resolve eq27 eq23516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq23516
  have eq23896 : x ≠ (k y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1103 y x
       have i₂ := eq11505
       grind)
    | exact superpose eq11505 eq1103
    | (have j0 := eq1103 y x
       grind)
    | exact resolve eq1103 eq11505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq11505
  have eq24027 : x ≠ (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq23896
       have i₂ := eq23497 y
       grind)
    | exact superpose eq23497 eq23896
    | exact resolve eq23896 eq23497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23497 eq23896
  have eq24072 : x ≠ (k x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq24027
       have i₂ := eq23494 x
       grind)
    | exact superpose eq23494 eq24027
    | exact resolve eq24027 eq23494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24027
  have eq24108 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq24072
       have r₂ := eq6481
       grind)
    | exact resolve eq24072 eq6481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24072
  have eq24126 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq24108
       have i₂ := eq23494 x
       grind)
    | exact superpose eq23494 eq24108
    | exact resolve eq24108 eq23494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23494 eq24108
  have eq24137 : x = (M.op x y) := by
    first
    | (have i₁ := eq24126
       have i₂ := eq6481
       grind)
    | exact superpose eq6481 eq24126
    | exact resolve eq24126 eq6481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6481 eq24126
  have eq24147 : x = (M.op x y) := by
    first
    | (have i₁ := eq24137
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24137
    | exact resolve eq24137 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq24137
  have eq24400 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq24147
       grind)
    | exact superpose eq24147 eq22
    | exact resolve eq22 eq24147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24147
  have eq24894 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq24400 eq20
    | exact resolve eq20 eq24400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq24400
  have eq24962 : False := by grind
  exact eq24962

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
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
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq14 X0 x x X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq64 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq78 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq70
    | (have j0 := eq70 (σ X0) (σ X1)
       grind)
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq76
    | (have j1 := eq70 y x
       grind)
    | exact resolve eq76 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq112 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
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
  have eq131 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq133 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq70 sF1 (σ X0)
       grind)
    | exact superpose eq70 eq37
    | (have j1 := eq70 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq130 eq16
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq155 : (k (σ (M.op x y)) (σ y)) = (σ (M.op y (M.op x y))) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq131
       have i₂ := eq70 sF0 y
       grind)
    | exact superpose eq70 eq131
    | (have j1 := eq70 (M.op x y) y
       grind)
    | exact resolve eq131 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq193 : (σ (k (k x (M.op x y)) (M.op x y))) = (k (k (σ x) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq45 eq41
    | exact resolve eq41 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq207 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq50 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y)
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq216 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq207 eq14
    | exact resolve eq14 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq208 eq14
    | exact resolve eq14 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq255 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq70 (τ X1) X0
       grind)
    | exact superpose eq70 eq34
    | (have j1 := eq70 (τ X1) X0
       grind)
    | exact resolve eq34 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq377 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq635 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (σ X1) (σ X0) X2
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq52
    | (have j1 := eq84 X0 X1
       grind)
    | exact resolve eq52 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X1) (M.op (σ (k X0 X1)) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (σ X1) (σ X0) x
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq53
    | (have j1 := eq84 X0 X1
       grind)
    | exact resolve eq53 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq84
  have eq872 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq100 eq70
    | (have j0 := eq70 (σ y) (σ x)
       grind)
    | exact resolve eq70 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq872
    | exact resolve eq872 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq876 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq873
       have r₂ := eq27
       grind)
    | exact resolve eq873 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq879 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq876 eq266
    | exact resolve eq266 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq881 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq876 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq876
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq876
       grind)
    | exact resolve eq13 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq876 eq52
    | exact resolve eq52 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq893 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq881
  have eq952 : (τ (σ x)) = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq893 eq60
    | exact resolve eq60 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq893
  have eq954 : x = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq952
    | exact resolve eq952 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq995 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq70 x y
       have i₂ := eq954
       grind)
    | exact superpose eq954 eq70
    | (have j0 := eq70 y x
       grind)
    | exact resolve eq70 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq996 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq995
  have eq998 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq996
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq996
    | exact resolve eq996 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1001 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq255 x
       have i₂ := eq998
       grind)
    | exact superpose eq998 eq255
    | exact resolve eq255 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1004 : x ≠ x ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq998
       grind)
    | exact superpose eq998 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq998
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq998
       grind)
    | exact resolve eq13 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1016 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq1004
  have eq1020 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1001 eq207
    | exact resolve eq207 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1085 : x ≠ (M.op x y) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1020 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq1020
       grind)
    | exact resolve eq13 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1919 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq879 eq887
    | exact resolve eq887 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879 eq887
  have eq1944 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1919
  have eq1993 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1944 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1944
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1944
       grind)
    | exact resolve eq13 eq1944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq2014 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1993
  have eq2017 : (τ (σ x)) = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2014 eq49
    | exact resolve eq49 eq2014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014
  have eq2021 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq2017
    | exact resolve eq2017 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017
  have eq2066 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq70 x x
       have i₂ := eq2021
       grind)
    | exact superpose eq2021 eq70
    | (have j0 := eq70 x x
       grind)
    | exact resolve eq70 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021
  have eq2067 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq2066
  have eq2073 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq265 y
       have i₂ := eq2067
       grind)
    | exact superpose eq2067 eq265
    | exact resolve eq265 eq2067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2081 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq52 y x X0
       have i₂ := eq2067
       grind)
    | exact superpose eq2067 eq52
    | exact resolve eq52 eq2067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067
  have eq3094 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2073 eq2081
    | exact resolve eq2081 eq2073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073 eq2081
  have eq3123 : x = (M.op x x) := by grind
  clear eq3094
  have eq3213 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq265 x
       have i₂ := eq3123
       grind)
    | exact superpose eq3123 eq265
    | exact resolve eq265 eq3123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3214 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq3123
       grind)
    | exact superpose eq3123 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq3123
       grind)
    | exact resolve eq13 eq3123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3235 : x = (k x x) := by grind
  clear eq3214
  have eq3348 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq3235
       grind)
    | exact superpose eq3235 eq43
    | exact resolve eq43 eq3235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3352 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3348
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3348
    | exact resolve eq3348 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3348
  have eq3355 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3352 eq70
    | (have j0 := eq70 (σ x) (σ x)
       grind)
    | exact resolve eq70 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3356 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3355
  have eq3373 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq3356 eq52
    | exact resolve eq52 eq3356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3941 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (k (M.op x y) X0)) (M.op (σ (M.op x y)) X1)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq133 eq52
    | (have j1 := eq133 X0
       grind)
    | exact resolve eq52 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq133
  have eq3970 : ∀ X0 : G, (k (k (σ x) (σ x)) (σ X0)) = (σ (M.op X0 (k x x))) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq49 eq349
    | exact resolve eq349 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq349
  have eq4018 : ∀ X0 : G, (k (k (σ x) (σ x)) (σ X0)) = (σ (M.op X0 x)) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3970 X0
       have i₂ := eq3235
       grind)
    | exact superpose eq3235 eq3970
    | (have j0 := eq3970 X0
       grind)
    | exact resolve eq3970 eq3235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3970
  have eq4022 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (M.op X0 x)) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq3352 eq4018
    | (have j0 := eq4018 X0
       grind)
    | exact resolve eq4018 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4018
  have eq4023 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op X0 x)) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq35 eq4022
    | (have j0 := eq4022 X0
       grind)
    | exact resolve eq4022 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq4022
  have eq4024 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op X0 x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4023 X0
       have i₂ := eq3235
       grind)
    | exact superpose eq3235 eq4023
    | (have j0 := eq4023 X0
       grind)
    | exact resolve eq4023 eq3235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4023
  have eq5254 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (σ (k (k x x) X0)) (M.op (k (σ x) (σ x)) X1)) ∨ (σ X0) = (M.op (k (σ x) (σ x)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq635 (k x x) X1 x
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq635
    | exact resolve eq635 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq635
  have eq5297 : ∀ X0 X1 : G, (σ x) = (M.op (σ (k (k x x) X0)) (M.op (σ x) X1)) ∨ (σ X0) = (M.op (k (σ x) (σ x)) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq3352 eq5254
    | (have j0 := eq5254 X0 X1
       grind)
    | exact resolve eq5254 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5254
  have eq5336 : ∀ X0 X1 : G, (σ x) = (M.op (σ (k x X0)) (M.op (σ x) X1)) ∨ (σ X0) = (M.op (k (σ x) (σ x)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5297 X0 X1
       have i₂ := eq3235
       grind)
    | exact superpose eq3235 eq5297
    | (have j0 := eq5297 X0 X1
       grind)
    | exact resolve eq5297 eq3235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3235 eq5297
  have eq5366 : ∀ X0 X1 : G, (σ x) = (M.op (σ (k x X0)) (M.op (σ x) X1)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq3352 eq5336
    | (have j0 := eq5336 X0 X1
       grind)
    | exact resolve eq5336 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352 eq5336
  have eq5507 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (M.op (σ (M.op X0 X1)) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq636 X0 X1 X2
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq636
    | (have j0 := eq636 X1 X0 X2
       have j1 := eq70 (σ X1) (σ X0)
       grind)
    | exact resolve eq636 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq8175 : ∀ X0 : G, (σ x) = (M.op (σ (k x X0)) (M.op (σ x) (σ y))) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq234 eq5366
    | (have j0 := eq5366 X0 (σ y)
       grind)
    | exact resolve eq5366 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq5366
  have eq8710 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4024 y
       have i₂ := eq1016
       grind)
    | exact superpose eq1016 eq4024
    | (have j0 := eq4024 y
       grind)
    | exact resolve eq4024 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq8723 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq4024 sF0
       grind)
    | exact superpose eq4024 eq45
    | (have j1 := eq4024 (M.op x y)
       grind)
    | exact resolve eq45 eq4024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq4024
  have eq8809 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3213 eq8723
    | exact resolve eq8723 eq3213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8723
  have eq8814 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8710
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8710
    | exact resolve eq8710 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8710
  have eq8820 : y = (M.op x y) ∨ (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8814
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8814
    | exact resolve eq8814 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8814
  have eq8821 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) := by grind
  clear eq8820
  have eq8959 : (k (σ (M.op x y)) (σ x)) = (σ (k (M.op x y) (M.op y x))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37 (M.op y x)
       have i₂ := eq8821
       grind)
    | exact superpose eq8821 eq37
    | exact resolve eq37 eq8821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq8975 : ∀ X0 : G, (τ (k X0 (σ x))) = (k (τ X0) (M.op y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq352 X0 (M.op y x)
       have i₂ := eq8821
       grind)
    | exact superpose eq8821 eq352
    | exact resolve eq352 eq8821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq8821
  have eq9006 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1001 eq8809
    | exact resolve eq8809 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9009 : (τ (k (σ x) (σ (M.op x y)))) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8809 eq16
    | exact resolve eq16 eq8809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8809
  have eq9051 : (k x (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64 eq9009
    | exact resolve eq9009 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq9009
  have eq9052 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9006
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9006
    | exact resolve eq9006 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9006
  have eq9765 : (τ (k (σ (M.op x y)) (σ x))) = (k (M.op x y) (M.op y x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8959 eq16
    | exact resolve eq16 eq8959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8959
  have eq9806 : (k (M.op x y) x) = (k (M.op x y) (M.op y x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq150 eq9765
    | exact resolve eq9765 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq9765
  have eq9822 : (k (M.op x y) x) = (M.op (M.op y x) (M.op x y)) ∨ (M.op y x) = (M.op (M.op x y) (M.op y x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9806 eq70
    | (have j0 := eq70 (M.op x y) (M.op y x)
       grind)
    | exact resolve eq70 eq9806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9806
  have eq9840 : x = (k (M.op x y) x) ∨ (M.op y x) = (M.op (M.op x y) (M.op y x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq265 eq9822
    | exact resolve eq9822 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq9822
  have eq9850 : y = (M.op y x) ∨ x = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq255 eq9840
    | exact resolve eq9840 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq9840
  have eq12336 : ∀ X0 : G, (τ (k (σ X0) (σ x))) = (k X0 (M.op y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8975 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq8975
    | exact resolve eq8975 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8975
  have eq12394 : ∀ X0 : G, (k X0 (τ (σ x))) = (k X0 (M.op y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12336 X0
       have i₂ := eq377 X0 sF2
       grind)
    | exact superpose eq377 eq12336
    | exact resolve eq12336 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq12336
  have eq12411 : ∀ X0 : G, (k X0 x) = (k X0 (M.op y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq12394
    | exact resolve eq12394 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12394
  have eq12548 : ∀ X0 : G, (k X0 x) = (k X0 y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12411 X0
       have i₂ := eq9850
       grind)
    | exact superpose eq9850 eq12411
    | exact resolve eq12411 eq9850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9850 eq12411
  have eq12597 : ∀ X0 : G, (k X0 x) = (k X0 y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) x) := by
    intro X0
    first
    | (have j0 := eq12548 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12548
  have eq21536 : (k (k (σ x) (σ (M.op x y))) (σ (M.op x y))) = (σ (k (M.op (M.op x y) x) (M.op x y))) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq193
       have i₂ := eq70 x sF0
       grind)
    | exact superpose eq70 eq193
    | (have j1 := eq70 x (M.op x y)
       grind)
    | exact resolve eq193 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq21596 : (k (k (σ x) (σ (M.op x y))) (σ (M.op x y))) = (σ (k (M.op (M.op x y) x) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3213 eq21536
    | exact resolve eq21536 eq3213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21536
  have eq26582 : (σ x) = (M.op (σ (M.op (M.op x y) x)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9051 eq8175
    | (have j0 := eq8175 (M.op x y)
       grind)
    | exact resolve eq8175 eq9051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8175 eq9051
  have eq26654 : (σ x) = (M.op (σ (M.op (M.op x y) x)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq26582
    | exact resolve eq26582 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26582
  have eq27229 : (k (k (σ x) (σ (M.op x y))) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op (M.op x y) x))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq21596
       have i₂ := eq70 (M.op sF0 x) sF0
       grind)
    | exact superpose eq70 eq21596
    | (have j1 := eq70 (M.op (M.op x y) x) (M.op x y)
       grind)
    | exact resolve eq21596 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq21596
  have eq27294 : x = (M.op x y) ∨ (k (k (σ x) (σ (M.op x y))) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op (M.op x y) x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq207 eq27229
    | exact resolve eq27229 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq27229
  have eq27295 : (k (k (σ x) (σ (M.op x y))) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op (M.op x y) x))) ∨ x = (M.op x y) := by grind
  clear eq27294
  have eq28205 : (M.op (M.op x y) (M.op (M.op x y) x)) = (τ (k (k (σ x) (σ (M.op x y))) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27295 eq16
    | exact resolve eq16 eq27295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27295
  have eq29002 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1020 eq155
    | exact resolve eq155 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq1020
  have eq29058 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29002
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29002
    | exact resolve eq29002 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29002
  have eq29060 : (τ (σ x)) = (k (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29058 eq158
    | exact resolve eq158 eq29058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq29058
  have eq29070 : y = (M.op (M.op x y) y) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq29060
    | exact resolve eq29060 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29060
  have eq29083 : y ≠ y ∨ y = (k y (M.op x y)) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29070 eq13
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq29070
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq29070
       grind)
    | exact resolve eq13 eq29070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29070
  have eq29108 : y = (k y (M.op x y)) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq29083
  have eq41587 : (τ (k (σ y) (σ (M.op x y)))) = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9052 eq28205
    | exact resolve eq28205 eq9052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9052 eq28205
  have eq41639 : (τ (k (σ y) (σ (M.op x y)))) = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq41587
  have eq41642 : (k y (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq112 eq41639
    | exact resolve eq41639 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq41639
  have eq48982 : (M.op (M.op x y) x) = (M.op (k y (M.op x y)) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41642 eq210
    | exact resolve eq210 eq41642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq41642
  have eq52510 : (M.op y x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29108 eq48982
    | exact resolve eq48982 eq29108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29108 eq48982
  have eq52549 : (M.op y x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) := by grind
  clear eq52510
  have eq52552 : (M.op y x) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | (have r₁ := eq52549
       have r₂ := eq1085
       grind)
    | exact resolve eq52549 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52549
  have eq64223 : (M.op x y) = (M.op x (M.op y x)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq52552 eq216
    | exact resolve eq216 eq52552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq52552
  have eq102295 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq64223
       have i₂ := eq998
       grind)
    | exact superpose eq998 eq64223
    | exact resolve eq64223 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998 eq64223
  have eq102336 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) := by grind
  clear eq102295
  have eq102340 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | (have i₁ := eq102336
       have i₂ := eq3123
       grind)
    | exact superpose eq3123 eq102336
    | exact resolve eq102336 eq3123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102336
  have eq102341 : x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq102340
       have r₂ := eq1085
       grind)
    | exact resolve eq102340 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085 eq102340
  have eq102758 : x = (k (M.op x y) x) ∨ y = (M.op x y) ∨ x = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq102341 eq12597
    | exact resolve eq12597 eq102341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12597 eq102341
  have eq102772 : x = (k (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq102758
  have eq102880 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq102772 eq3941
    | (have j0 := eq3941 x x
       grind)
    | exact resolve eq3941 eq102772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3941 eq102772
  have eq102912 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq102880 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102880
    | (have j0 := eq102880 X0
       grind)
    | exact resolve eq102880 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102880
  have eq102932 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq102912 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102912
    | (have j0 := eq102912 X0
       grind)
    | exact resolve eq102912 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102912
  have eq703606 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26654 eq5507
    | (have j0 := eq5507 (M.op x y) x x
       grind)
    | exact resolve eq5507 eq26654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5507 eq26654
  have eq703667 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq703606
    | exact resolve eq703606 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703606
  have eq703669 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq703667
    | exact resolve eq703667 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703667
  have eq703670 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq703669
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq703669
    | exact resolve eq703669 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703669
  have eq703671 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq703670
  have eq703672 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3213 eq703671
    | exact resolve eq703671 eq3213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703671
  have eq703673 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq703672
  have eq802157 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1001 eq703673
    | exact resolve eq703673 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703673
  have eq802503 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq802157
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq802157
    | exact resolve eq802157 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802157
  have eq843497 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq802503 eq102932
    | exact resolve eq102932 eq802503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102932 eq802503
  have eq843565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq843497
  have eq843573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq843565
    | exact resolve eq843565 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843565
  have eq843579 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq843573
       have r₂ := eq27
       grind)
    | exact resolve eq843573 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843573
  have eq843600 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq843579 eq3373
    | exact resolve eq3373 eq843579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3373
  have eq843704 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq843600 eq843579
    | exact resolve eq843579 eq843600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843579 eq843600
  have eq843785 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq843704
  have eq843804 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq843785 eq29
    | exact resolve eq29 eq843785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq843785
  have eq845178 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq843804
    | exact resolve eq843804 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843804
  have eq845385 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq845178 eq28
    | exact resolve eq28 eq845178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq845178
  have eq846700 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq845385
    | exact resolve eq845385 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq845385
  have eq846701 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq846700
  have eq846894 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq846701 eq3213
    | exact resolve eq3213 eq846701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3213 eq846701
  have eq847333 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq846894
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq846894
    | exact resolve eq846894 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846894
  have eq847334 : x = (M.op x y) ∨ x = y := by grind
  clear eq847333
  have eq847559 : y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq847334 eq1001
    | exact resolve eq1001 eq847334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq847334
  have eq848405 : y = (M.op x x) ∨ x = y := by grind
  clear eq847559
  have eq848703 : x = y ∨ x = y := by
    first
    | (have i₁ := eq848405
       have i₂ := eq3123
       grind)
    | exact superpose eq3123 eq848405
    | exact resolve eq848405 eq3123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848405
  have eq848704 : x = y := by grind
  clear eq848703
  have eq848976 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq848704
       grind)
    | exact superpose eq848704 eq18
    | exact resolve eq18 eq848704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq848977 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq848704
       grind)
    | exact superpose eq848704 eq24
    | exact resolve eq24 eq848704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq848704
  have eq850378 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq848977
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq848977
    | exact resolve eq848977 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848977
  have eq850379 : x = (M.op x y) := by
    first
    | (have i₁ := eq848976
       have i₂ := eq3123
       grind)
    | exact superpose eq3123 eq848976
    | exact resolve eq848976 eq3123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3123 eq848976
  have eq850775 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq850378 eq26
    | exact resolve eq26 eq850378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq850378
  have eq851891 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3356 eq850775
    | exact resolve eq850775 eq3356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3356 eq850775
  have eq852270 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq850379 eq20
    | exact resolve eq20 eq850379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq850379
  have eq853264 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq852270
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq852270
    | exact resolve eq852270 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq852270
  have eq853881 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq851891 eq27
    | exact resolve eq27 eq851891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq851891
  have eq857354 : False := by grind
  exact eq857354

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pxx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
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
  clear eq35
  have eq51 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq67 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq102 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq110 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq113 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq113 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq113 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq114 (σ X0)
       grind)
    | exact superpose eq114 eq10
    | exact resolve eq10 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq43
    | exact resolve eq43 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq118 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq114 y
       grind)
    | exact superpose eq114 eq76
    | exact resolve eq76 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq121 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq114 sF3
       grind)
    | exact superpose eq114 eq118
    | exact resolve eq118 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq114 sF2
       grind)
    | exact superpose eq114 eq117
    | exact resolve eq117 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq123 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq116 X0
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq116
    | exact resolve eq116 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq130 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq102
       have i₂ := eq114 sF3
       grind)
    | exact superpose eq114 eq102
    | exact resolve eq102 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq131 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq130
       have i₂ := eq114 y
       grind)
    | exact superpose eq114 eq130
    | exact resolve eq130 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq141 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq144 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq141
       have i₂ := eq114 sF1
       grind)
    | exact superpose eq114 eq141
    | exact resolve eq141 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq147 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq144
       have i₂ := eq114 sF0
       grind)
    | exact superpose eq114 eq144
    | exact resolve eq144 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq144
  have eq169 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq147 eq16
    | exact resolve eq16 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq314 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq316 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y) X0
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq363 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq316 eq51
    | exact resolve eq51 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq780 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq123 X1
       grind)
    | exact superpose eq123 eq78
    | (have j0 := eq78 X0 X1
       grind)
    | exact resolve eq78 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq123
  have eq923 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ y)) = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq780 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq780
    | (have j0 := eq780 y X0
       grind)
    | exact resolve eq780 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq6465 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq923 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq923
    | (have j0 := eq923 x
       grind)
    | exact resolve eq923 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq923
  have eq6495 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6465
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq6465
    | exact resolve eq6465 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6465
  have eq6513 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq6495
    | exact resolve eq6495 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6495
  have eq6521 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6513
       have i₂ := eq122
       grind)
    | exact superpose eq122 eq6513
    | exact resolve eq6513 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6513
  have eq6530 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq6521
    | exact resolve eq6521 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6521
  have eq6534 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq6530
    | exact resolve eq6530 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6530
  have eq10487 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq10487
    | exact resolve eq10487 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10487
  have eq10499 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10488
       have r₂ := eq27
       grind)
    | exact resolve eq10488 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10488
  have eq10503 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq10499
    | exact resolve eq10499 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10499
  have eq10505 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq10503
    | exact resolve eq10503 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10503
  have eq10507 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10505 eq110
    | (have r₁ := eq110
       have r₂ := eq10505
       grind)
    | exact resolve eq110 eq10505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10505
  have eq10553 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq10507
  have eq10554 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq10553
  have eq10694 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10554 eq97
    | exact resolve eq97 eq10554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10554
  have eq10705 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10694
  have eq10707 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10705
       have r₂ := eq27
       grind)
    | exact resolve eq10705 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10705
  have eq10709 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq10707
       grind)
    | exact superpose eq10707 eq109
    | (have r₁ := eq109
       have r₂ := eq10707
       grind)
    | exact resolve eq109 eq10707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10710 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq122
       have i₂ := eq10707
       grind)
    | exact superpose eq10707 eq122
    | exact resolve eq122 eq10707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq10707
  have eq10755 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10709
  have eq10756 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10755
  have eq10770 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10710
    | exact resolve eq10710 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10710
  have eq10857 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq10756
       grind)
    | exact superpose eq10756 eq75
    | exact resolve eq75 eq10756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10756
  have eq10877 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10857
    | exact resolve eq10857 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10857
  have eq11163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10877 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10877
  have eq11166 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11163
    | exact resolve eq11163 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11163
  have eq11177 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11166
       have r₂ := eq27
       grind)
    | exact resolve eq11166 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11166
  have eq11181 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11177
    | exact resolve eq11177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11177
  have eq11183 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11181
    | exact resolve eq11181 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq11181
  have eq11184 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11183
  have eq11225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11184 eq10770
    | exact resolve eq10770 eq11184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10770 eq11184
  have eq11264 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11225
  have eq11274 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11264
       have r₂ := eq27
       grind)
    | exact resolve eq11264 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11264
  have eq11277 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11274 eq27
    | exact resolve eq27 eq11274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11279 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11274 eq67
    | (have r₁ := eq67
       have r₂ := eq11274
       grind)
    | exact resolve eq67 eq11274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq11291 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11274 eq316
    | exact resolve eq316 eq11274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11274
  have eq11308 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11279
  have eq11393 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11291 eq11291
    | exact resolve eq11291 eq11291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11291
  have eq11426 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11393
  have eq11461 : (τ (σ y)) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11426 eq131
    | exact resolve eq131 eq11426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11527 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq11461
    | exact resolve eq11461 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11461
  have eq11806 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11308 eq93
    | exact resolve eq93 eq11308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq11807 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11308 eq97
    | exact resolve eq97 eq11308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq11308
  have eq11821 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq11807
  have eq11832 : (k y x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq11806
    | exact resolve eq11806 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq11806
  have eq11835 : (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq11832
       have r₂ := eq66
       grind)
    | exact resolve eq11832 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq11832
  have eq12604 : (k (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11835
       grind)
    | exact superpose eq11835 eq75
    | exact resolve eq75 eq11835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq12626 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12604
       have i₂ := eq121
       grind)
    | exact superpose eq121 eq12604
    | exact resolve eq12604 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq12604
  have eq28798 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12626 eq6534
    | exact resolve eq6534 eq12626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6534
  have eq29060 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq28798 eq316
    | exact resolve eq316 eq28798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28798
  have eq29798 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29060 eq110
    | (have r₁ := eq110
       have r₂ := eq29060
       grind)
    | exact resolve eq110 eq29060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq29060
  have eq29854 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq29798
  have eq29855 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq29854
  have eq29864 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12626 eq29855
    | exact resolve eq29855 eq12626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12626 eq29855
  have eq30156 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29864 eq316
    | exact resolve eq316 eq29864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq29864
  have eq30202 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq30156
  have eq30424 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30202 eq363
    | exact resolve eq363 eq30202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq30202
  have eq38149 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11821 eq11426
    | exact resolve eq11426 eq11821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11426 eq11821
  have eq38261 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq38149
  have eq38279 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq38261
       have r₂ := eq11277
       grind)
    | exact resolve eq38261 eq11277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11277 eq38261
  have eq38302 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq38279
       grind)
    | exact superpose eq38279 eq109
    | (have r₁ := eq109
       have r₂ := eq38279
       grind)
    | exact resolve eq109 eq38279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq38279
  have eq38360 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq38302
  have eq38361 : y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq38360
  have eq38381 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq38361
       have i₂ := eq11835
       grind)
    | exact superpose eq11835 eq38361
    | exact resolve eq38361 eq11835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11835 eq38361
  have eq38971 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11527
       have i₂ := eq38381
       grind)
    | exact superpose eq38381 eq11527
    | exact resolve eq11527 eq38381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11527 eq38381
  have eq39074 : y = (M.op x y) := by grind
  clear eq38971
  have eq39123 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq39074 eq20
    | exact resolve eq20 eq39074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq39280 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq39123
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39123
    | exact resolve eq39123 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39123
  have eq39440 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39280 eq30424
    | exact resolve eq30424 eq39280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30424
  have eq39493 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq39440
       have r₂ := eq27
       grind)
    | exact resolve eq39440 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39440
  have eq39643 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq39493 eq169
    | exact resolve eq169 eq39493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq39493
  have eq39710 : (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq39074 eq39643
    | exact resolve eq39643 eq39074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39643
  have eq39958 : y = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq314 y
       have i₂ := eq39710
       grind)
    | exact superpose eq39710 eq314
    | exact resolve eq314 eq39710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40026 : y = (M.op y (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq39074 eq39958
    | exact resolve eq39958 eq39074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39958
  have eq40186 : y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq40026 eq314
    | exact resolve eq314 eq40026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq40026
  have eq40234 : y = (M.op y y) := by
    first
    | exact superpose eq39074 eq40186
    | exact resolve eq40186 eq39074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39074 eq40186
  have eq40245 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq40234
       have i₂ := eq39710
       grind)
    | exact superpose eq39710 eq40234
    | exact resolve eq40234 eq39710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39710 eq40234
  have eq40267 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40245 eq15
    | exact resolve eq15 eq40245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40245
  have eq40368 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40267
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40267
    | exact resolve eq40267 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq40267
  have eq40405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39280 eq40368
    | exact resolve eq40368 eq39280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39280 eq40368
  have eq40438 : False := by grind
  exact eq40438
