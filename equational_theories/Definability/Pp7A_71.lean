import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq73
    | exact resolve eq73 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq73
  have eq99 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq99 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq99
    | exact resolve eq99 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq103 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq100
  have eq153 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq158 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq153 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq153
    | (have j0 := eq153 X0 X1
       grind)
    | exact resolve eq153 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq653 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq158 x y
       grind)
    | exact superpose eq158 eq16
    | (have j1 := eq158 x y
       grind)
    | exact resolve eq16 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq1096 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq155 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq155
    | exact resolve eq155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq1154 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1096 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1096
    | (have j0 := eq1096 X0 X1
       grind)
    | exact resolve eq1096 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096
  have eq5387 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq653
       have i₂ := eq1154 y x
       grind)
    | exact superpose eq1154 eq653
    | (have j1 := eq1154 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq653
       have r₂ := eq1154 y x
       grind)
    | (have r₁ := eq653
       have r₂ := eq1154 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq653
       have r₂ := eq1154 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq653 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq1154
  have eq5388 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq5387
  have eq5390 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5388
       grind)
    | exact superpose eq5388 eq16
    | exact resolve eq16 eq5388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5388
  have eq5391 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5390
       have r₂ := eq80 x
       grind)
    | exact resolve eq5390 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5390
  have eq5397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq5391
       grind)
    | exact superpose eq5391 eq103
    | exact resolve eq103 eq5391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5391
  have eq5414 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5397
       have r₂ := eq16
       grind)
    | exact resolve eq5397 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5397
  have eq5417 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5414
       grind)
    | exact superpose eq5414 eq10
    | exact resolve eq10 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5414
  have eq5471 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5417
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5417
    | exact resolve eq5417 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5417
  have eq5474 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5471
       grind)
    | exact superpose eq5471 eq16
    | exact resolve eq16 eq5471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5471
  have eq5475 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5474
       have r₂ := eq80 x
       grind)
    | exact resolve eq5474 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq5474
  have eq5482 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq5475
       grind)
    | exact superpose eq5475 eq10
    | exact resolve eq10 eq5475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5475
  have eq5536 : y = (M.op x x) := by
    first
    | (have i₁ := eq5482
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5482
    | exact resolve eq5482 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5482
  have eq5551 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq5536
       grind)
    | exact superpose eq5536 eq103
    | exact resolve eq103 eq5536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq5536
  have eq5568 : False := by grind
  exact eq5568

/-- `Equation3888`: `x ◇ x = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation3888 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3888 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3888.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq94 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq98 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq94
  have eq99 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq98
  have eq884 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq70
  have eq989 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq884 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq7589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq78 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq7589
    | exact resolve eq7589 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7589
  have eq7601 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq7590
       have r₂ := eq28
       grind)
    | exact resolve eq7590 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7590
  have eq7605 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq7601
    | exact resolve eq7601 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7601
  have eq7616 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (M.op (σ x) (σ y)) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq7605 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7605
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq7605
       grind)
    | exact resolve eq12 eq7605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7605
  have eq8875 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq7616
    | (have j0 := eq7616 (σ x)
       grind)
    | (have r₁ := eq7616 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq7616 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7616
  have eq8876 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq8875
  have eq8877 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq8876
  have eq8892 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq8877 eq78
    | exact resolve eq78 eq8877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq8877
  have eq8902 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8892
  have eq8905 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8902
       have r₂ := eq28
       grind)
    | exact resolve eq8902 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8902
  have eq8909 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq8905
       grind)
    | exact superpose eq8905 eq99
    | exact resolve eq99 eq8905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8918 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq8905
       grind)
    | exact superpose eq8905 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8905
       grind)
    | exact resolve eq12 eq8905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8905
  have eq8952 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq8909
    | exact resolve eq8909 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8909
  have eq9831 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8918 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8918
    | (have j0 := eq8918 x
       grind)
    | (have r₁ := eq8918 x
       have r₂ := eq19
       grind)
    | exact resolve eq8918 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8918
  have eq9832 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq9831
  have eq9833 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq9832
  have eq10788 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq989 x y
       have i₂ := eq9833
       grind)
    | exact superpose eq9833 eq989
    | (have j0 := eq989 x y
       grind)
    | exact resolve eq989 eq9833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989 eq9833
  have eq10792 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10788
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq10788
    | exact resolve eq10788 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10788
  have eq10801 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq10792
    | exact resolve eq10792 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10792
  have eq10805 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10801
       have r₂ := eq8952
       grind)
    | exact resolve eq10801 eq8952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10801
  have eq10807 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10805
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq10805
    | exact resolve eq10805 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq10805
  have eq10809 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10807
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10807
    | exact resolve eq10807 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10807
  have eq10811 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10809
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10809
    | exact resolve eq10809 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10809
  have eq10813 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq10811
    | exact resolve eq10811 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10811
  have eq10815 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10813
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10813
    | exact resolve eq10813 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10813
  have eq10817 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10815
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10815
    | exact resolve eq10815 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10815
  have eq10818 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10817
  have eq10872 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10818 eq8952
    | exact resolve eq8952 eq10818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8952 eq10818
  have eq10900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10872
  have eq10911 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq10900
       have r₂ := eq28
       grind)
    | exact resolve eq10900 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10900
  have eq11021 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq10911 eq30
    | exact resolve eq30 eq10911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10911
  have eq11125 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq11021
    | exact resolve eq11021 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11021
  have eq11126 : x = y := by grind
  clear eq11125
  have eq11143 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq11126
       grind)
    | exact superpose eq11126 eq19
    | exact resolve eq19 eq11126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq11144 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq11126
       grind)
    | exact superpose eq11126 eq25
    | exact resolve eq25 eq11126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11126
  have eq11249 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11144
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11144
    | exact resolve eq11144 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11144
  have eq11264 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11249 eq27
    | exact resolve eq27 eq11249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq11249
  have eq11633 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11264 eq69
    | exact resolve eq69 eq11264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq11264
  have eq11687 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11633
       have i₂ := eq11143
       grind)
    | exact superpose eq11143 eq11633
    | exact resolve eq11633 eq11143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11143 eq11633
  have eq11734 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11687 eq15
    | exact resolve eq15 eq11687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11687
  have eq11781 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11734
    | exact resolve eq11734 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq11734
  have eq11790 : False := by grind
  exact eq11790

/-- `Equation3897`: `x ◇ x = (y ◇ (z ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pyx_pxx_pyx_Equation3897 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3897 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3897.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq39 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq49 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq49 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq50 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq50 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq50 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq59 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq39 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X0 X0 X2
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq39 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq54 X1 X0
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq56 X1 X0
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq67 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X1 x
       have i₂ := eq9 X1 x X0
       grind)
    | exact superpose eq9 eq59
    | (have j0 := eq59 X0 X1 x
       grind)
    | exact resolve eq59 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq124 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq128 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       have j1 := eq67 X1 X0
       grind)
    | (have r₁ := eq124 X1 X0
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq124 X1 X1
       have r₂ := eq67 X1 X1
       grind)
    | exact resolve eq124 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq124
  have eq365 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq128 (σ X1) (σ X0)
       grind)
    | exact superpose eq128 eq15
    | exact resolve eq15 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 X1
       have i₂ := eq128 X1 X0
       grind)
    | exact superpose eq128 eq365
    | exact resolve eq365 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq365
  have eq376 : False := by grind
  exact eq376

/-- `Equation3897`: `x ◇ x = (y ◇ (z ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pyx_pyy_pyx_Equation3897 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3897 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3897.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq264 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq264 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq264 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq264 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq276 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq265 (σ X0)
       grind)
    | exact superpose eq265 eq15
    | exact resolve eq15 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq265 (τ X0)
       grind)
    | exact superpose eq265 eq31
    | exact resolve eq31 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq289 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq282 X0
       have i₂ := eq265 X0
       grind)
    | exact superpose eq265 eq282
    | exact resolve eq282 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq295 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq276 X0
       have i₂ := eq265 X0
       grind)
    | exact superpose eq265 eq276
    | exact resolve eq276 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq276
  have eq510 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq527 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq510 X0 X1
       have i₂ := eq295 X0
       grind)
    | exact superpose eq295 eq510
    | (have j0 := eq510 X0 X1
       grind)
    | exact resolve eq510 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq652 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq527 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq527
    | exact resolve eq527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq693 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq652
    | (have j0 := eq652 X0 X1
       grind)
    | exact resolve eq652 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq652
  have eq699 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq693 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq693 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq693 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq693 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq702 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq699
  have eq704 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq702
    | (have j0 := eq702 X0 X1
       grind)
    | exact resolve eq702 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq705 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq704 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq704
    | exact resolve eq704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq704 (σ X0) X1
       grind)
    | exact superpose eq704 eq15
    | (have j1 := eq704 (σ X0) X1
       grind)
    | exact resolve eq15 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq736 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 X1
       have i₂ := eq295 X0
       grind)
    | exact superpose eq295 eq712
    | (have j0 := eq712 X0 X1
       grind)
    | exact resolve eq712 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq767 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq705 (τ X1) X0
       grind)
    | exact superpose eq705 eq17
    | (have j1 := eq705 (τ X1) X0
       grind)
    | exact resolve eq17 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq705
  have eq912 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq767 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq767
    | exact resolve eq767 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq965 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq912 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq912
    | (have j0 := eq912 X0 X1
       grind)
    | exact resolve eq912 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq2632 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq736 x y
       grind)
    | exact superpose eq736 eq16
    | (have j1 := eq736 x y
       grind)
    | exact resolve eq16 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2650 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq736 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq2684 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2632
       have i₂ := eq965 y x
       grind)
    | exact superpose eq965 eq2632
    | (have j1 := eq965 y x
       grind)
    | (have r₁ := eq2632
       have r₂ := eq965 y x
       grind)
    | exact resolve eq2632 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2632
  have eq2685 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2684
  have eq2688 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2685
       grind)
    | exact superpose eq2685 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2685
       grind)
    | exact resolve eq13 eq2685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2689 : y ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2685
       grind)
    | exact superpose eq2685 eq12
    | exact resolve eq12 eq2685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq2691 : y = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2688
  have eq2692 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2691
       have r₂ := eq2689
       grind)
    | exact resolve eq2691 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689 eq2691
  have eq2717 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2650 x y
       have i₂ := eq2692
       grind)
    | exact superpose eq2692 eq2650
    | (have j0 := eq2650 x y
       grind)
    | exact resolve eq2650 eq2692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650 eq2692
  have eq2740 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2717
  have eq2741 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2740
  have eq2825 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2741
       grind)
    | exact superpose eq2741 eq16
    | exact resolve eq16 eq2741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2827 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2741
       grind)
    | exact superpose eq2741 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq2741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2828 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2741
       grind)
    | exact superpose eq2741 eq12
    | exact resolve eq12 eq2741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2741
  have eq2831 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2828
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2828
    | exact resolve eq2828 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828
  have eq2832 : (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2827
       have r₂ := eq295 x
       grind)
    | exact resolve eq2827 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2827
  have eq2833 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2832
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2832
    | exact resolve eq2832 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2832
  have eq2834 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2833
       have i₂ := eq295 x
       grind)
    | exact superpose eq295 eq2833
    | exact resolve eq2833 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq2833
  have eq2835 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2834
       have r₂ := eq2831
       grind)
    | exact resolve eq2834 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831 eq2834
  have eq2843 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq965 y x
       have i₂ := eq2835
       grind)
    | exact superpose eq2835 eq965
    | (have j0 := eq965 y x
       grind)
    | exact resolve eq965 eq2835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965 eq2835
  have eq2893 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2843
       have r₂ := eq2825
       grind)
    | exact resolve eq2843 eq2825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2843
  have eq2956 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2825
       have i₂ := eq2893
       grind)
    | exact superpose eq2893 eq2825
    | exact resolve eq2825 eq2893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2825 eq2893
  have eq2961 : False := by grind
  exact eq2961

/-- `Equation3897`: `x ◇ x = (y ◇ (z ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation3897 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3897 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3897.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq85 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq193 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq85 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq85 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq85 X1 X1
       grind)
    | exact resolve eq13 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq196 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq197 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq197 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq197
    | (have j0 := eq197 X0 X1
       grind)
    | exact resolve eq197 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq206 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       have j1 := eq195 X1 X0
       grind)
    | (have r₁ := eq199 X1 X0
       have r₂ := eq195 X0 X1
       grind)
    | (have r₁ := eq199 (k X1 X0) X1
       have r₂ := eq195 X0 X1
       grind)
    | (have r₁ := eq199 X1 X1
       have r₂ := eq195 X1 X1
       grind)
    | exact resolve eq199 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq199
  have eq546 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq206 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq206
    | exact resolve eq206 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq206 y x
       grind)
    | exact superpose eq206 eq16
    | (have j1 := eq206 y x
       grind)
    | exact resolve eq16 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq574 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq546
    | (have j0 := eq546 X0 X1
       grind)
    | exact resolve eq546 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq546
  have eq575 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq574 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq574
    | exact resolve eq574 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq638 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq575 (τ X1) X0
       grind)
    | exact superpose eq575 eq18
    | (have j1 := eq575 (τ X1) X0
       grind)
    | exact resolve eq18 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq575
  have eq1015 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq638 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq638
    | exact resolve eq638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq1071 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1015 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1015
    | (have j0 := eq1015 X0 X1
       grind)
    | exact resolve eq1015 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1178 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq560
       have i₂ := eq1071 y x
       grind)
    | exact superpose eq1071 eq560
    | (have j1 := eq1071 (σ y) (σ x)
       grind)
    | (have r₁ := eq560
       have r₂ := eq1071 y x
       grind)
    | exact resolve eq560 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1179 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1178
  have eq1183 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1179
  have eq1216 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq560
       have i₂ := eq1183
       grind)
    | exact superpose eq1183 eq560
    | exact resolve eq560 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq1183
  have eq1217 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1216
  have eq1218 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1217
  have eq1229 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1218
  have eq1240 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1229
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1229
    | exact resolve eq1229 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1389 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1240
       grind)
    | exact superpose eq1240 eq16
    | exact resolve eq16 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq1449 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1389
       have i₂ := eq1071 y x
       grind)
    | exact superpose eq1071 eq1389
    | (have j1 := eq1071 y x
       grind)
    | (have r₁ := eq1389
       have r₂ := eq1071 y x
       grind)
    | exact resolve eq1389 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1450 : y = (M.op x x) := by grind
  clear eq1449
  have eq1517 : (M.op x y) = (k y x) := by grind
  clear eq1450
  have eq1529 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1389
       have i₂ := eq1517
       grind)
    | exact superpose eq1517 eq1389
    | exact resolve eq1389 eq1517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389 eq1517
  have eq1533 : False := by grind
  exact eq1533

/-- `Equation3897`: `x ◇ x = (y ◇ (z ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation3897 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3897 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3897.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq19
  have eq153 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq155 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq740 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq153 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq769 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq155 X0 X1
       grind)
    | exact superpose eq155 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq155 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq155 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq155 (M.op (τ X1) X0) X1
       grind)
    | exact resolve eq13 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq776 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq769 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq777 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq776 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq2300 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq777 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq777
    | exact resolve eq777 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq2355 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2300 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2300
    | (have j0 := eq2300 X0 X1
       grind)
    | exact resolve eq2300 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2300
  have eq2397 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq2355 X1 X0
       grind)
    | exact superpose eq2355 eq10
    | (have j1 := eq2355 X1 X0
       grind)
    | exact resolve eq10 eq2355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2441 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2397 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2397
    | (have j0 := eq2397 X0 X1
       grind)
    | exact resolve eq2397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397
  have eq2479 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq2441 X0 (σ X1)
       grind)
    | exact superpose eq2441 eq37
    | (have j1 := eq2441 X0 (σ X1)
       grind)
    | exact resolve eq37 eq2441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2441
  have eq4298 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq2479 (σ X0) X1
       grind)
    | exact superpose eq2479 eq28
    | (have j1 := eq2479 (σ X0) X1
       grind)
    | exact resolve eq28 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2479
  have eq4359 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4298 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4298
    | (have j0 := eq4298 X0 X1
       grind)
    | exact resolve eq4298 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4298
  have eq4393 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4359 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4359
    | (have j0 := eq4359 X0 X1
       grind)
    | exact resolve eq4359 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4359
  have eq4403 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4393 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4393
    | (have j0 := eq4393 X0 X1
       grind)
    | exact resolve eq4393 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4393
  have eq4608 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq4403 X1 X0
       grind)
    | exact superpose eq4403 eq11
    | (have j1 := eq4403 X1 X0
       grind)
    | exact resolve eq11 eq4403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4403
  have eq5502 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4608 y x
       grind)
    | exact superpose eq4608 eq16
    | (have j1 := eq4608 y x
       grind)
    | exact resolve eq16 eq4608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4608
  have eq5534 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5502
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq5502
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq5502
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5502
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5502 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5535 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq5502
       have i₂ := eq2355 y x
       grind)
    | exact superpose eq2355 eq5502
    | (have j1 := eq2355 y x
       grind)
    | (have r₁ := eq5502
       have r₂ := eq2355 y x
       grind)
    | (have r₁ := eq5502
       have r₂ := eq2355 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5502
       have r₂ := eq2355 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5502 eq2355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2355 eq5502
  have eq5538 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5535
  have eq5539 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq5538
  have eq5540 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5534
  have eq5541 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq5540
  have eq5545 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5539
       grind)
    | exact superpose eq5539 eq16
    | exact resolve eq16 eq5539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5539
  have eq5546 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5545
       have r₂ := eq22 x
       grind)
    | exact resolve eq5545 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5545
  have eq5550 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq740 x y
       have i₂ := eq5546
       grind)
    | exact superpose eq5546 eq740
    | (have j0 := eq740 x y
       grind)
    | exact resolve eq740 eq5546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740 eq5546
  have eq5557 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5550
  have eq5558 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5557
  have eq5562 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5541
       grind)
    | exact superpose eq5541 eq16
    | exact resolve eq16 eq5541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5541
  have eq5563 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5562
       have r₂ := eq22 x
       grind)
    | exact resolve eq5562 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5562
  have eq5572 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5558
       grind)
    | exact superpose eq5558 eq16
    | exact resolve eq16 eq5558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5558
  have eq5593 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5572
       have i₂ := eq5563
       grind)
    | exact superpose eq5563 eq5572
    | exact resolve eq5572 eq5563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5563 eq5572
  have eq5594 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq5593
  have eq5595 : (σ x) = (σ y) := by grind
  clear eq5594
  have eq5596 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5595
       grind)
    | exact superpose eq5595 eq16
    | exact resolve eq16 eq5595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5597 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5595
       grind)
    | exact superpose eq5595 eq10
    | exact resolve eq10 eq5595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5595
  have eq5652 : x = y := by
    first
    | (have i₁ := eq5597
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5597
    | exact resolve eq5597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5597
  have eq5653 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5596
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5596
    | exact resolve eq5596 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5596
  have eq5654 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5653
       have i₂ := eq5652
       grind)
    | exact superpose eq5652 eq5653
    | exact resolve eq5653 eq5652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5652 eq5653
  have eq5655 : False := by grind
  exact eq5655

/-- `Equation3912`: `x ◇ x = (y ◇ (z ◇ w)) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_pxx_pxy_Equation3912 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X3)) X3) := by
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
  have eq176 : ∀ X0 X1 X2 X5 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X0)) X5) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq16 X1 X2 (M.op x (M.op x X5)) X5
       have i₂ := eq16 X0 x x X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op x y)) y) := by
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
  have eq178 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X5 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq16 X1 (M.op x (M.op x (M.op x X5))) x X5
       have i₂ := eq16 X0 x x (M.op x X5)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq181 X1 X0
       grind)
    | (have i₁ := eq13 X1 X2
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq13
    | (have j0 := eq13 X1 X2
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq181 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op x y)) y) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 x X3
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq177 (M.op X0 X0) X1
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq177
    | exact resolve eq177 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq256 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 x X3
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq178 (M.op X0 X0) X1
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq454 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1482 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 (M.op X0 X0) X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq1524 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (k (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X0 X2 X1 X3
       have i₂ := eq1482 X0 X1
       grind)
    | exact superpose eq1482 eq176
    | exact resolve eq176 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1550 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X1 X2 (M.op X0 X0)
       have i₂ := eq1482 X0 (M.op X1 X1)
       grind)
    | exact superpose eq1482 eq180
    | exact resolve eq180 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1646 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (σ x) (σ y))) (σ y)) = (M.op (k (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq256 x (M.op x x) X3
       have i₂ := eq1524 X0 X1 (M.op x x) X2
       grind)
    | exact superpose eq1524 eq256
    | exact resolve eq256 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1647 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op x y)) y) = (M.op (k (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq255 x (M.op x x) X3
       have i₂ := eq1524 X0 X1 (M.op x x) X2
       grind)
    | exact superpose eq1524 eq255
    | exact resolve eq255 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq1524
  have eq1702 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq11
    | (have j0 := eq11 X0 (k X1 X1)
       grind)
    | exact resolve eq11 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1740 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq181 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq181
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1793 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq1794 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq1811 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1740 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq1825 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1702 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1702
  have eq2169 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (k X0 X0) X3) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq180 X2 X1 X3
       have i₂ := eq1825 X2 X0
       grind)
    | exact superpose eq1825 eq180
    | (have j1 := eq1825 X1 (M.op (k X0 X0) X3)
       grind)
    | exact resolve eq180 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2172 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X1 X2
       have i₂ := eq1825 X2 X0
       grind)
    | exact superpose eq1825 eq181
    | (have j1 := eq1825 X1 X0
       grind)
    | exact resolve eq181 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2224 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1825 X0 (σ X1)
       grind)
    | exact superpose eq1825 eq10
    | (have j1 := eq1825 X0 (σ (k X1 X1))
       grind)
    | exact resolve eq10 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2227 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1825 X0 (τ X1)
       grind)
    | exact superpose eq1825 eq34
    | (have j1 := eq1825 X0 (τ X1)
       grind)
    | exact resolve eq34 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq2231 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2227 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq2227
    | (have j0 := eq2227 X0 X1
       grind)
    | exact resolve eq2227 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227
  have eq8927 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1793
       grind)
    | exact superpose eq1793 eq40
    | exact resolve eq40 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1793
  have eq8928 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8927
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8927
    | exact resolve eq8927 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8927
  have eq8930 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq8928
    | exact resolve eq8928 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8928
  have eq41218 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2169 X1 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41282 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41218 X2 X1 (k X1 X1)
       have i₂ := eq181 (k X1 X1) X0
       grind)
    | (have i₁ := eq41218 X2 X1 (k X1 X1)
       have i₂ := eq181 X0 (k X1 X1)
       grind)
    | exact superpose eq181 eq41218
    | (have j0 := eq41218 X2 X1 X2
       grind)
    | (have r₁ := eq41218 X0 (M.op X1 X1) (k (M.op X1 X1) (M.op X1 X1))
       have r₂ := eq181 (k (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq41218 X0 (M.op X0 X0) (k (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq181 X0 (k (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq41218 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41315 : ∀ X0 X1 X2 X3 : G, (k X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 ∨ (M.op X3 X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq41218 X2 X1 (k X1 X1)
       have i₂ := eq2172 X0 (k X1 X1) X3
       grind)
    | exact superpose eq2172 eq41218
    | (have j0 := eq41218 X2 X1 X2
       have j1 := eq2172 X1 X1 X2
       grind)
    | (have r₁ := eq41218 X0 (k X0 X0) (k (k X0 X0) (k X0 X0))
       have r₂ := eq2172 X0 (k (k X0 X0) (k X0 X0)) X2
       grind)
    | (have r₁ := eq41218 X0 X0 (k X0 X0)
       have r₂ := eq2172 X0 X1 (k X0 X0)
       grind)
    | (have r₁ := eq41218 X0 (M.op X2 X2) X2
       have r₂ := eq2172 (M.op (k (M.op X2 X2) (M.op X2 X2)) X2) X1 X2
       grind)
    | exact resolve eq41218 eq2172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41218
  have eq49720 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2224 X1 (M.op X2 X2)
       have i₂ := eq1550 X2 X2 X0
       grind)
    | exact superpose eq1550 eq2224
    | (have j0 := eq2224 X1 (M.op X0 X0)
       grind)
    | exact resolve eq2224 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550 eq2224
  have eq50604 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq2231 X0 (σ X1)
       grind)
    | exact superpose eq2231 eq10
    | (have j1 := eq2231 X0 (σ X1)
       grind)
    | exact resolve eq10 eq2231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231
  have eq50778 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50604 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq50604
    | (have j0 := eq50604 X0 X1
       grind)
    | exact resolve eq50604 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50604
  have eq62151 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X1) = X2 ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50778 X0 X2
       have i₂ := eq50778 X1 X2
       grind)
    | exact superpose eq50778 eq50778
    | (have j0 := eq50778 X1 X2
       have j1 := eq50778 X1 X2
       grind)
    | exact resolve eq50778 eq50778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50778
  have eq62572 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq62151 X0 X1 X2
       have j1 := eq41282 X0 X2 X1
       grind)
    | (have r₁ := eq62151 X0 X0 X1
       have r₂ := eq41282 X0 X1 X2
       grind)
    | (have r₁ := eq62151 X0 X1 (M.op X0 X0)
       have r₂ := eq41282 X0 (M.op X1 X1) X2
       grind)
    | (have r₁ := eq62151 X0 X1 X1
       have r₂ := eq41282 X0 X1 X2
       grind)
    | exact resolve eq62151 eq41282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62151
  have eq67010 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X1 X1)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq62572 X0 X1 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67011 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq62572 X0 X0 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62572
  have eq67014 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq67011 X0 x
       have j1 := eq49720 X0 X0 X0
       grind)
    | (have r₁ := eq67011 x X0
       have r₂ := eq49720 X0 x x
       grind)
    | (have r₁ := eq67011 x x
       have r₂ := eq49720 X0 x x
       grind)
    | exact resolve eq67011 eq49720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67011
  have eq67015 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq67010 X0 X1
       have j1 := eq49720 X0 X1 X0
       grind)
    | (have r₁ := eq67010 X0 X0
       have r₂ := eq49720 X0 X0 x
       grind)
    | (have r₁ := eq67010 X0 x
       have r₂ := eq49720 X0 x x
       grind)
    | exact resolve eq67010 eq49720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49720 eq67010
  have eq67728 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq67015 (k (M.op x x) x) X1
       have i₂ := eq1647 x x (k (M.op x x) x) X0
       grind)
    | exact superpose eq1647 eq67015
    | exact resolve eq67015 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq67729 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq67015 (k (M.op x x) x) X1
       have i₂ := eq1646 x x (k (M.op x x) x) X0
       grind)
    | exact superpose eq1646 eq67015
    | exact resolve eq67015 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq68027 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X1 X1)
       have i₂ := eq67015 X1 X0
       grind)
    | exact superpose eq67015 eq15
    | exact resolve eq15 eq67015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8930 eq1794
    | exact resolve eq1794 eq8930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794 eq8930
  have eq123885 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq123876
       have r₂ := eq27
       grind)
    | exact resolve eq123876 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123876
  have eq123892 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1825 eq123885
    | (have j1 := eq1825 (σ x) (σ x)
       grind)
    | exact resolve eq123885 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825 eq123885
  have eq123895 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1811 eq123892
    | (have j1 := eq1811 x x
       grind)
    | exact resolve eq123892 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811 eq123892
  have eq123903 : (τ (σ y)) = (k x x) ∨ (σ x) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq123895 eq97
    | exact resolve eq97 eq123895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq123895
  have eq123944 : y = (k x x) ∨ (σ x) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31 eq123903
    | exact resolve eq123903 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq123903
  have eq123961 : (σ x) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq41315 y y x x
       grind)
    | (have r₁ := eq123944
       have r₂ := eq41315 x y x x
       grind)
    | (have r₁ := eq123944
       have r₂ := eq41315 x (σ x) x x
       grind)
    | exact resolve eq123944 eq41315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41315 eq123944
  have eq123996 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (σ x) X1) ∨ x = (M.op X2 X2) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2169 x X0 X2 X1
       have i₂ := eq123961
       grind)
    | exact superpose eq123961 eq2169
    | (have j0 := eq2169 (M.op (σ x) X1) X1 X0 x
       grind)
    | exact resolve eq2169 eq123961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169
  have eq124028 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) X1) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq123996 X0 X1 x
       have j1 := eq41282 X0 (M.op (σ x) X1) X0
       grind)
    | (have r₁ := eq123996 X0 X1 x
       have r₂ := eq41282 X0 (M.op (σ x) X1) x
       grind)
    | (have r₁ := eq123996 X0 (σ x) x
       have r₂ := eq41282 (σ x) (M.op X0 X0) x
       grind)
    | (have r₁ := eq123996 X0 X1 X0
       have r₂ := eq41282 X0 x x
       grind)
    | exact resolve eq123996 eq41282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123996
  have eq124042 : ∀ X1 : G, (k x x) = (M.op (σ x) X1) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X1
    first
    | exact superpose eq2172 eq124028
    | (have j1 := eq2172 y X1 x
       grind)
    | exact resolve eq124028 eq2172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172 eq124028
  have eq124049 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X1
    first
    | exact superpose eq123961 eq124042
    | exact resolve eq124042 eq123961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123961 eq124042
  have eq124255 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq124049 eq68027
    | exact resolve eq68027 eq124049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68027 eq124049
  have eq124556 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq124255
    | exact resolve eq124255 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124255
  have eq124793 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq124556 x
       have j1 := eq41282 x y x
       grind)
    | (have r₁ := eq124556 x
       have r₂ := eq41282 x x x
       grind)
    | (have r₁ := eq124556 x
       have r₂ := eq41282 x y x
       grind)
    | (have r₁ := eq124556 x
       have r₂ := eq41282 x x x
       grind)
    | exact resolve eq124556 eq41282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41282 eq124556
  have eq125000 : ∀ X0 : G, (M.op X0 X0) = y ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq124793
       have i₂ := eq181 x x
       grind)
    | (have i₁ := eq124793
       have i₂ := eq181 X0 x
       grind)
    | exact superpose eq181 eq124793
    | exact resolve eq124793 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125016 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq181 X0 x
       have i₂ := eq124793
       grind)
    | exact superpose eq124793 eq181
    | exact resolve eq181 eq124793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125114 : y = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq67014 x
       have i₂ := eq124793
       grind)
    | exact superpose eq124793 eq67014
    | exact resolve eq67014 eq124793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124793
  have eq125244 : x = (M.op x x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq125114
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq125114
    | exact resolve eq125114 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125114
  have eq125620 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x X1) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq180 x X0 X1
       have i₂ := eq125244
       grind)
    | exact superpose eq125244 eq180
    | exact resolve eq180 eq125244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq125622 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq181 X0 x
       have i₂ := eq125244
       grind)
    | exact superpose eq125244 eq181
    | exact resolve eq181 eq125244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq125720 : x = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq67014 x
       have i₂ := eq125244
       grind)
    | exact superpose eq125244 eq67014
    | exact resolve eq67014 eq125244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125244
  have eq125813 : y = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq125720
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq125720
    | exact resolve eq125720 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125720
  have eq125873 : ∀ X1 : G, x = (M.op x X1) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq125622 eq125620
    | exact resolve eq125620 eq125622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125620
  have eq125947 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq125813 eq125873
    | exact resolve eq125873 eq125813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125873
  have eq127050 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq67728 sF0 x
       have i₂ := eq125622 sF0
       grind)
    | exact superpose eq125622 eq67728
    | exact resolve eq67728 eq125622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67728
  have eq127067 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x (σ y)) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq256 X0 X1 sF4
       have i₂ := eq125622 sF4
       grind)
    | exact superpose eq125622 eq256
    | exact resolve eq256 eq125622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq127288 : ∀ X1 : G, (M.op x X1) = (M.op x (σ y)) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq125622 eq127067
    | exact resolve eq127067 eq125622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127067
  have eq127299 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq127050 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq127050
    | (have j0 := eq127050 X0
       grind)
    | exact resolve eq127050 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127050
  have eq127658 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X1) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq125813 eq127288
    | exact resolve eq127288 eq125813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127288
  have eq127669 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq127299
    | (have j0 := eq127299 X0
       grind)
    | exact resolve eq127299 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127299
  have eq127954 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X1) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq26 eq127658
    | (have j0 := eq127658 X1
       grind)
    | exact resolve eq127658 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127658
  have eq127962 : x = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq125622 eq127669
    | exact resolve eq127669 eq125622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125622 eq127669
  have eq128142 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq125947 eq127954
    | (have j1 := eq125947 (σ y)
       grind)
    | exact resolve eq127954 eq125947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125947 eq127954
  have eq128148 : (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq125813 eq127962
    | exact resolve eq127962 eq125813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125813 eq127962
  have eq128250 : (σ (M.op x y)) ≠ (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq128142 eq27
    | exact resolve eq27 eq128142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128142
  have eq128329 : y = (σ y) := by
    first
    | (have r₁ := eq128250
       have r₂ := eq128148
       grind)
    | exact resolve eq128250 eq128148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128148 eq128250
  have eq128361 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq128329
       grind)
    | exact superpose eq128329 eq18
    | exact resolve eq18 eq128329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq128362 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq128329
       grind)
    | exact superpose eq128329 eq24
    | exact resolve eq24 eq128329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128500 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (σ y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq128362 eq454
    | exact resolve eq454 eq128362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq136995 : ∀ X0 X1 : G, (M.op X0 X0) = (σ y) ∨ x = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67015 X1 X0
       have i₂ := eq125000 X1
       grind)
    | exact superpose eq125000 eq67015
    | (have j1 := eq125000 X1
       grind)
    | exact resolve eq67015 eq125000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67015 eq125000
  have eq137618 : ∀ X0 X1 : G, x = (M.op X1 X1) ∨ (M.op X0 X0) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq136995 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq136995
    | (have j0 := eq136995 X0 X1
       grind)
    | exact resolve eq136995 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq136995
  have eq138816 : ∀ X0 : G, x = (σ x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq67014 x
       have i₂ := eq125016 X0
       grind)
    | exact superpose eq125016 eq67014
    | (have j1 := eq125016 X0
       grind)
    | exact resolve eq67014 eq125016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67014 eq125016
  have eq138958 : ∀ X0 : G, x = (σ x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq138816 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq138816
    | (have j0 := eq138816 X0
       grind)
    | exact resolve eq138816 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138816
  have eq139110 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq138958 X0
       have i₂ := eq128329
       grind)
    | exact superpose eq128329 eq138958
    | exact resolve eq138958 eq128329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128329 eq138958
  have eq139605 : ∀ X1 : G, (k (σ y) X1) = (M.op X1 (σ y)) ∨ x = (σ x) := by
    intro X1
    first
    | (have i₁ := eq1482 x X1
       have i₂ := eq139110 x
       grind)
    | exact superpose eq139110 eq1482
    | exact resolve eq1482 eq139110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148410 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x (σ y))) ∨ (σ y) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67729 sF4 X1
       have i₂ := eq137618 X0 sF4
       grind)
    | exact superpose eq137618 eq67729
    | (have j1 := eq137618 X1 X1
       grind)
    | exact resolve eq67729 eq137618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67729
  have eq148626 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (σ y) = (M.op X1 X1) := by
    intro X0 X1
    first
    | exact superpose eq128361 eq148410
    | (have j0 := eq148410 X0 X1
       grind)
    | exact resolve eq148410 eq128361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148410
  have eq149060 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (σ y) = (M.op X1 X1) := by
    intro X0 X1
    first
    | exact superpose eq20 eq148626
    | (have j0 := eq148626 X0 X1
       grind)
    | exact resolve eq148626 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148626
  have eq149410 : ∀ X1 : G, x = (σ (M.op x y)) ∨ (σ y) = (M.op X1 X1) := by
    intro X1
    first
    | exact superpose eq137618 eq149060
    | (have j0 := eq149060 x X1
       have j1 := eq137618 X1 X1
       grind)
    | exact resolve eq149060 eq137618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137618 eq149060
  have eq149635 : ∀ X1 : G, (σ y) = (M.op X1 X1) ∨ (σ (M.op x y)) = (σ x) := by
    intro X1
    first
    | exact superpose eq139110 eq149410
    | (have j0 := eq149410 X1
       have j1 := eq139110 X1
       grind)
    | exact resolve eq149410 eq139110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139110 eq149410
  have eq149990 : ∀ X1 : G, (k (σ y) X1) = (M.op X1 (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X1
    first
    | (have i₁ := eq1482 X1 X1
       have i₂ := eq149635 X1
       grind)
    | exact superpose eq149635 eq1482
    | exact resolve eq1482 eq149635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482 eq149635
  have eq168434 : (M.op x y) = (k (σ y) x) ∨ x = (σ x) := by
    first
    | exact superpose eq139605 eq128361
    | exact resolve eq128361 eq139605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168436 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (σ x) := by
    first
    | exact superpose eq139605 eq26
    | (have j1 := eq139605 (σ x)
       grind)
    | exact resolve eq26 eq139605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139605
  have eq169620 : (τ (M.op (σ x) (σ y))) = (k (σ y) (τ (σ x))) ∨ x = (σ x) := by
    first
    | exact superpose eq168436 eq128500
    | exact resolve eq128500 eq168436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128500 eq168436
  have eq169627 : (τ (M.op (σ x) (σ y))) = (k (σ y) x) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq169620
    | exact resolve eq169620 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq169620
  have eq169633 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    first
    | exact superpose eq168434 eq169627
    | exact resolve eq169627 eq168434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168434 eq169627
  have eq169640 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq169633 eq14
    | exact resolve eq14 eq169633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169633
  have eq169689 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq169640
    | exact resolve eq169640 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169640
  have eq169690 : x = (σ x) := by
    first
    | (have r₁ := eq169689
       have r₂ := eq27
       grind)
    | exact resolve eq169689 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169689
  have eq169692 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq22
       have i₂ := eq169690
       grind)
    | exact superpose eq169690 eq22
    | exact resolve eq22 eq169690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq169694 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq169690
       grind)
    | exact superpose eq169690 eq39
    | exact resolve eq39 eq169690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq169725 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq128361
       have i₂ := eq169690
       grind)
    | exact superpose eq169690 eq128361
    | exact resolve eq128361 eq169690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128361 eq169690
  have eq169752 : (σ x) = (τ (σ x)) := by
    first
    | exact superpose eq169692 eq15
    | exact resolve eq15 eq169692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169692
  have eq170092 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq169725 eq26
    | exact resolve eq26 eq169725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq170124 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq170092 eq27
    | exact resolve eq27 eq170092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq170092
  have eq187929 : (M.op x y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq149990 eq169725
    | exact resolve eq169725 eq149990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149990 eq169725
  have eq189280 : (σ (M.op x y)) = (k (σ (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq187929 eq169694
    | exact resolve eq169694 eq187929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169694
  have eq189284 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq128362 eq189280
    | exact resolve eq189280 eq128362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128362 eq189280
  have eq189293 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq189284
    | exact resolve eq189284 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq189284
  have eq189302 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq187929 eq189293
    | exact resolve eq189293 eq187929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187929 eq189293
  have eq189311 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq189302
       have r₂ := eq170124
       grind)
    | exact resolve eq189302 eq170124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189302
  have eq189314 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq189311 eq28
    | exact resolve eq28 eq189311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq189363 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq189311 eq170124
    | exact resolve eq170124 eq189311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170124 eq189311
  have eq189503 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq189314 eq169752
    | exact resolve eq169752 eq189314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169752 eq189314
  have eq189570 : False := by grind
  exact eq189570

/-- `Equation3912`: `x ◇ x = (y ◇ (z ◇ w)) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_pyx_pxy_Equation3912 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X3)) X3) := by
    intro X0 X1 X2 X3
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
  have eq51 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op (M.op X4 (M.op X5 X6)) X6) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq14 x X4 X5 X6
       have i₂ := eq14 x X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op (M.op X4 (M.op (M.op X0 (M.op X1 X2)) X2)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 X4 X5 X5
       have i₂ := eq14 X5 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op x y)) y) := by
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
  have eq57 : ∀ X0 X1 X5 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq14 X1 (M.op x (M.op x (M.op x X5))) x X5
       have i₂ := eq14 X0 x x (M.op x X5)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq58 X1 X0
       grind)
    | (have i₁ := eq13 X1 X2
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq13
    | (have j0 := eq13 X1 X2
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq58 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq58 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq90 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq97 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq100 : ∀ X0 : G, (σ (k X0 (k y y))) = (k (σ X0) (k (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k y y)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq10
    | exact resolve eq10 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0
       have i₂ := eq58 X0 X1
       grind)
    | (have i₁ := eq85 X1
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq85
    | exact resolve eq85 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq114 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq122 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq122
  have eq135 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq121
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq121
    | exact resolve eq121 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq136 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq135
    | exact resolve eq135 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq148 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq182 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq148 eq16
    | exact resolve eq16 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k (M.op X1 X1) X2) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X1) X2
       have i₂ := eq57 X1 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq57 X0 X1 x
       grind)
    | exact superpose eq57 eq13
    | (have j0 := eq13 (M.op X1 X1) X2
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X0) x) X1
       have r₂ := eq57 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq57 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X1 X2 : G, (k (M.op X1 X1) X2) = (M.op X2 (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq295 x X1 X2
       grind)
    | (have r₁ := eq295 x X1 X2
       have r₂ := eq58 x X1
       grind)
    | (have r₁ := eq295 X1 x X2
       have r₂ := eq58 x X1
       grind)
    | exact resolve eq295 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq347 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 X6)) X6) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X3 X4 X5 X6
    first
    | (have i₁ := eq51 (M.op x X3) x X3 X4 X5 X6
       have i₂ := eq57 X0 (M.op x X3) X1
       grind)
    | (have i₁ := eq51 (M.op X0 X0) X1 x X4 X5 X6
       have i₂ := eq57 X0 X1 (M.op X1 x)
       grind)
    | exact superpose eq57 eq51
    | exact resolve eq51 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq744 : ∀ X0 X1 X2 X4 X5 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op (M.op (M.op X0 (M.op x y)) y) X4)) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq52 (M.op x X4) x X4 X1 X2 X5
       have i₂ := eq54 (M.op x X4) X0
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq862 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq347 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq347
    | (have j0 := eq347 X0 x
       grind)
    | exact resolve eq347 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq887 : (k (k (M.op x y) (M.op x y)) x) = (τ (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x))) := by
    first
    | exact superpose eq182 eq862
    | exact resolve eq862 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq1172 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X0 X0
       have i₂ := eq58 (σ X0) X1
       grind)
    | (have i₁ := eq113 X0 X0
       have i₂ := eq58 X0 (σ X0)
       grind)
    | exact superpose eq58 eq113
    | exact resolve eq113 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1210 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq9845 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1210 X0 (τ X1)
       grind)
    | exact superpose eq1210 eq35
    | (have j1 := eq1210 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1210
  have eq9879 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9845 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq9845
    | (have j0 := eq9845 X0 X1
       grind)
    | exact resolve eq9845 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9845
  have eq9887 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9879 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq9879
    | (have j0 := eq9879 X0 X1
       grind)
    | exact resolve eq9879 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9879
  have eq11160 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq9887 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22031 : (τ (k (σ y) (σ y))) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq132
       grind)
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq22094 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq102 eq22031
    | exact resolve eq22031 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22031
  have eq22100 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq79 x y y
       grind)
    | (have r₁ := eq22094
       have r₂ := eq79 y (k y y) x
       grind)
    | (have r₁ := eq22094
       have r₂ := eq79 y y x
       grind)
    | exact resolve eq22094 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22094
  have eq22105 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq22100
       grind)
    | exact superpose eq22100 eq91
    | exact resolve eq91 eq22100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq22114 : ∀ X0 : G, y ≠ (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq11160 X0 y
       have i₂ := eq22100
       grind)
    | exact superpose eq22100 eq11160
    | (have j0 := eq11160 X0 y
       grind)
    | exact resolve eq11160 eq22100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22129 : ∀ X0 : G, (k (σ y) (σ y)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22105
       have i₂ := eq58 y X0
       grind)
    | (have i₁ := eq22105
       have i₂ := eq58 X0 y
       grind)
    | exact superpose eq58 eq22105
    | exact resolve eq22105 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22105
  have eq22211 : ∀ X0 : G, (k (σ y) (σ y)) = (σ (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | (have i₁ := eq22129 x
       have i₂ := eq54 x X0
       grind)
    | exact superpose eq54 eq22129
    | exact resolve eq22129 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22214 : ∀ X0 X1 : G, (k (σ y) (σ y)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22129 x
       have i₂ := eq57 X0 x X1
       grind)
    | (have i₁ := eq22129 (M.op X0 X0)
       have i₂ := eq57 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq22129
    | exact resolve eq22129 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22361 : ∀ X0 X1 : G, (M.op X0 X0) ≠ y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22114 X1
       have i₂ := eq58 y X0
       grind)
    | (have i₁ := eq22114 X1
       have i₂ := eq58 X0 y
       grind)
    | exact superpose eq58 eq22114
    | (have j0 := eq22114 X1
       grind)
    | exact resolve eq22114 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22114
  have eq22878 : ∀ X0 X1 : G, (k (k (σ y) (σ y)) (k (σ y) (σ y))) = (σ (k (M.op (M.op X0 X0) X1) (k y y))) := by
    intro X0 X1
    first
    | (have i₁ := eq100 (M.op (M.op X0 X0) X1)
       have i₂ := eq22214 X0 X1
       grind)
    | exact superpose eq22214 eq100
    | exact resolve eq100 eq22214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq22905 : ∀ X0 X1 : G, (k (k (σ y) (σ y)) (k (σ y) (σ y))) = (σ (k (M.op (M.op X0 X0) X1) (M.op y y))) := by
    intro X0 X1
    first
    | (have i₁ := eq22878 X0 X1
       have i₂ := eq22100
       grind)
    | exact superpose eq22100 eq22878
    | exact resolve eq22878 eq22100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22878
  have eq22918 : ∀ X0 X1 : G, (k (k (σ y) (σ y)) (k (σ y) (σ y))) = (σ (M.op (M.op y y) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22905 X0 X1
       have i₂ := eq103 y (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq103 eq22905
    | exact resolve eq22905 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq22905
  have eq22924 : (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq22918 x x
       have i₂ := eq22214 y (M.op (M.op x x) x)
       grind)
    | exact superpose eq22214 eq22918
    | exact resolve eq22918 eq22214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22214 eq22918
  have eq25103 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (M.op X0 X0) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq22924 eq9887
    | (have j0 := eq9887 X0 (σ y)
       grind)
    | exact resolve eq9887 eq22924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9887 eq22924
  have eq25110 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq25103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25103
  have eq25125 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq25110 x
       have i₂ := eq54 x X0
       grind)
    | exact superpose eq54 eq25110
    | exact resolve eq25110 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq25128 : ∀ X0 X1 : G, (k (σ y) (σ y)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25110 x
       have i₂ := eq57 X0 x X1
       grind)
    | (have i₁ := eq25110 (M.op X0 X0)
       have i₂ := eq57 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq25110
    | exact resolve eq25110 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25380 : ∀ X0 : G, (k y y) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq25110 eq102
    | exact resolve eq102 eq25110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq25110
  have eq25414 : ∀ X0 : G, (M.op y y) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq25380 X0
       have i₂ := eq22100
       grind)
    | exact superpose eq22100 eq25380
    | exact resolve eq25380 eq22100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25380
  have eq27384 : ∀ X1 X2 X4 X5 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op (k (σ y) (σ y)) X4)) X5) := by
    intro X1 X2 X4 X5
    first
    | exact superpose eq25125 eq744
    | exact resolve eq744 eq25125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq25125
  have eq28015 : ∀ X0 X4 X5 X6 X7 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op (M.op X5 X5) X6) X7) := by
    intro X0 X4 X5 X6 X7
    first
    | (have i₁ := eq593 X0 x x (M.op X5 X6) X5 X6
       have i₂ := eq27384 (M.op X5 X6) x X4 X5
       grind)
    | exact superpose eq27384 eq593
    | exact resolve eq593 eq27384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq27384
  have eq28071 : ∀ X0 X4 X7 : G, (M.op (M.op X0 X0) X4) = (M.op (k (σ y) (σ y)) X7) := by
    intro X0 X4 X7
    first
    | (have i₁ := eq28015 X0 X4 x x X7
       have i₂ := eq25128 x x
       grind)
    | exact superpose eq25128 eq28015
    | exact resolve eq28015 eq25128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28015
  have eq28182 : ∀ X7 : G, (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) X7) := by
    intro X7
    first
    | (have i₁ := eq28071 x x X7
       have i₂ := eq25128 x x
       grind)
    | exact superpose eq25128 eq28071
    | exact resolve eq28071 eq25128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25128 eq28071
  have eq60231 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq114 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq114
    | (have j0 := eq114 x
       grind)
    | exact resolve eq114 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq60267 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq60231
  have eq60288 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60267
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq60267
    | exact resolve eq60267 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq60267
  have eq60317 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq79 x (σ x) (σ x)
       grind)
    | (have r₁ := eq60288
       have r₂ := eq79 (σ x) (k (σ x) (σ x)) x
       grind)
    | (have r₁ := eq60288
       have r₂ := eq79 (σ x) (σ x) x
       grind)
    | exact resolve eq60288 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60288
  have eq60363 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq60317 eq50
    | exact resolve eq50 eq60317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq60317
  have eq60401 : (k x x) = (M.op y y) := by
    first
    | (have i₁ := eq60363
       have i₂ := eq25414 sF2
       grind)
    | exact superpose eq25414 eq60363
    | exact resolve eq60363 eq25414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60363
  have eq60436 : ∀ X0 : G, x ≠ (M.op y y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq11160 X0 x
       have i₂ := eq60401
       grind)
    | exact superpose eq60401 eq11160
    | (have j0 := eq11160 X0 x
       grind)
    | exact resolve eq11160 eq60401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11160 eq60401
  have eq60875 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq149
    | (have j0 := eq149 (M.op x y)
       grind)
    | exact resolve eq149 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq60909 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq60875
  have eq60928 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq148 eq60909
    | exact resolve eq60909 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq60909
  have eq60965 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq79 x (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq60928
       have r₂ := eq79 (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y))) x
       grind)
    | (have r₁ := eq60928
       have r₂ := eq79 (σ (M.op x y)) (σ (M.op x y)) x
       grind)
    | exact resolve eq60928 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60928
  have eq61065 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq60965 eq182
    | exact resolve eq182 eq60965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq61068 : (k (k (M.op x y) (M.op x y)) x) = (τ (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x))) := by
    first
    | exact superpose eq60965 eq887
    | exact resolve eq887 eq60965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq60965
  have eq61100 : (k (k (M.op x y) (M.op x y)) x) = (τ (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq61068
       have i₂ := eq306 sF1 sF2
       grind)
    | exact superpose eq306 eq61068
    | exact resolve eq61068 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61068
  have eq61103 : (M.op y y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq61065
       have i₂ := eq25414 sF1
       grind)
    | exact superpose eq25414 eq61065
    | exact resolve eq61065 eq25414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61065
  have eq89503 : (k (M.op y y) x) = (τ (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq61103 eq61100
    | exact resolve eq61100 eq61103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61100 eq61103
  have eq89504 : (M.op x (M.op y y)) = (τ (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq89503
       have i₂ := eq306 y x
       grind)
    | exact superpose eq306 eq89503
    | exact resolve eq89503 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq89503
  have eq94565 : ∀ X0 : G, (M.op x (M.op y y)) = (τ (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq89504
       have i₂ := eq58 sF1 x
       grind)
    | (have i₁ := eq89504
       have i₂ := eq58 X0 sF1
       grind)
    | exact superpose eq58 eq89504
    | exact resolve eq89504 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89504
  have eq141222 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq136 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq141229 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq141222
    | exact resolve eq141222 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141222
  have eq141240 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq141229
       have r₂ := eq28
       grind)
    | exact resolve eq141229 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141229
  have eq141297 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq141240 eq25414
    | exact resolve eq25414 eq141240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141240
  have eq141412 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq141297
    | exact resolve eq141297 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq141297
  have eq141442 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq22361 x y
       grind)
    | (have r₁ := eq141412
       have r₂ := eq22361 y x
       grind)
    | (have r₁ := eq141412
       have r₂ := eq22361 x x
       grind)
    | exact resolve eq141412 eq22361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22361 eq141412
  have eq141499 : (τ (σ x)) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq141442 eq25414
    | exact resolve eq25414 eq141442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141442
  have eq141612 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq141499
    | exact resolve eq141499 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141499
  have eq141638 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq60436 x
       grind)
    | (have r₁ := eq141612
       have r₂ := eq60436 x
       grind)
    | exact resolve eq141612 eq60436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60436 eq141612
  have eq141641 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq141638
       have i₂ := eq58 y X0
       grind)
    | (have i₁ := eq141638
       have i₂ := eq58 X0 y
       grind)
    | exact superpose eq58 eq141638
    | exact resolve eq141638 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141705 : x = (M.op x x) ∨ y = (τ y) := by
    first
    | (have i₁ := eq25414 y
       have i₂ := eq141638
       grind)
    | exact superpose eq141638 eq25414
    | exact resolve eq25414 eq141638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141638
  have eq143396 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (τ y) := by
    intro X0
    first
    | (have i₁ := eq141705
       have i₂ := eq58 x X0
       grind)
    | (have i₁ := eq141705
       have i₂ := eq58 X0 x
       grind)
    | exact superpose eq58 eq141705
    | exact resolve eq141705 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq143437 : (σ x) = (k (σ y) (σ y)) ∨ y = (τ y) := by
    first
    | (have i₁ := eq22129 x
       have i₂ := eq141705
       grind)
    | exact superpose eq141705 eq22129
    | exact resolve eq22129 eq141705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141705
  have eq143543 : (σ x) = (k (σ y) (σ y)) ∨ y = (τ y) := by
    first
    | (have i₁ := eq143437
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq143437
    | exact resolve eq143437 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143437
  have eq144024 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (τ y) := by
    first
    | (have i₁ := eq22211 sF0
       have i₂ := eq143396 sF0
       grind)
    | exact superpose eq143396 eq22211
    | exact resolve eq22211 eq143396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22211 eq143396
  have eq144249 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (τ y) := by
    first
    | (have i₁ := eq144024
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq144024
    | exact resolve eq144024 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144024
  have eq144473 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (τ y) := by
    first
    | exact superpose eq21 eq144249
    | exact resolve eq144249 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144249
  have eq145923 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (τ y) := by
    intro X0
    first
    | exact superpose eq143543 eq28182
    | exact resolve eq28182 eq143543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28182
  have eq149259 : (σ (M.op x y)) = (σ x) ∨ y = (τ y) ∨ y = (τ y) := by
    first
    | exact superpose eq144473 eq143543
    | exact resolve eq143543 eq144473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143543 eq144473
  have eq149298 : y = (τ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq149259
  have eq149342 : y = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq149298
       grind)
    | exact superpose eq149298 eq15
    | exact resolve eq15 eq149298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149298
  have eq149399 : (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq149342
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq149342
    | exact resolve eq149342 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149342
  have eq151903 : y = (τ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq145923
    | (have j0 := eq145923 (σ y)
       grind)
    | exact resolve eq145923 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145923
  have eq152334 : y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq151903
       grind)
    | exact superpose eq151903 eq15
    | exact resolve eq15 eq151903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151903
  have eq152391 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq152334
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq152334
    | exact resolve eq152334 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq152334
  have eq152394 : (σ (M.op x y)) ≠ (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq152391 eq28
    | exact resolve eq28 eq152391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152391
  have eq152417 : y = (σ y) := by
    first
    | (have r₁ := eq152394
       have r₂ := eq149399
       grind)
    | exact resolve eq152394 eq149399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149399 eq152394
  have eq152419 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq152417 eq27
    | exact resolve eq27 eq152417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq152429 : (k y x) = (τ (k y (σ x))) := by
    first
    | exact superpose eq152417 eq97
    | exact resolve eq97 eq152417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq156004 : ∀ X0 : G, (σ x) = (k (σ y) (σ y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq22129 x
       have i₂ := eq141641 X0
       grind)
    | exact superpose eq141641 eq22129
    | (have j1 := eq141641 X0
       grind)
    | exact resolve eq22129 eq141641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22129 eq141641
  have eq156136 : ∀ X0 : G, (σ x) = (k y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq152417 eq156004
    | (have j0 := eq156004 X0
       grind)
    | exact resolve eq156004 eq152417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152417 eq156004
  have eq156193 : ∀ X0 : G, (σ x) = (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq156136 X0
       have i₂ := eq22100
       grind)
    | exact superpose eq22100 eq156136
    | (have j0 := eq156136 X0
       grind)
    | exact resolve eq156136 eq22100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22100 eq156136
  have eq156233 : ∀ X0 : G, (σ x) = (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq156193 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq156193
    | (have j0 := eq156193 X0
       grind)
    | exact resolve eq156193 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq156193
  have eq158009 : ∀ X0 : G, (M.op (σ x) y) = (k y (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq85 y
       have i₂ := eq156233 X0
       grind)
    | (have i₁ := eq85 X0
       have i₂ := eq156233 X0
       grind)
    | exact superpose eq156233 eq85
    | (have j1 := eq156233 X0
       grind)
    | exact resolve eq85 eq156233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq158047 : ∀ X0 : G, (σ x) = (τ (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq25414 y
       have i₂ := eq156233 X0
       grind)
    | (have i₁ := eq25414 X0
       have i₂ := eq156233 X0
       grind)
    | exact superpose eq156233 eq25414
    | (have j1 := eq156233 X0
       grind)
    | exact resolve eq25414 eq156233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25414 eq156233
  have eq158172 : ∀ X0 : G, (M.op X0 X0) = y ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq29 eq158047
    | (have j0 := eq158047 X0
       grind)
    | exact resolve eq158047 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq158047
  have eq158194 : (M.op (σ x) y) = (k y (σ x)) := by
    first
    | (have j1 := eq79 x y (σ x)
       grind)
    | (have r₁ := eq158009 x
       have r₂ := eq79 x y x
       grind)
    | exact resolve eq158009 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq158009
  have eq158263 : (M.op (σ x) (σ y)) = (k y (σ x)) := by
    first
    | exact superpose eq152419 eq158194
    | exact resolve eq158194 eq152419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158194
  have eq158328 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq158263 eq152429
    | exact resolve eq152429 eq158263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152429
  have eq158637 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op y X2) ∨ x = (σ x) := by
    intro X0 X2
    first
    | (have i₁ := eq57 x X0 X2
       have i₂ := eq158172 x
       grind)
    | exact superpose eq158172 eq57
    | exact resolve eq57 eq158172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq162274 : ∀ X0 : G, y = (M.op y X0) ∨ x = (σ x) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq158172 x
       have i₂ := eq158637 x X0
       grind)
    | (have i₁ := eq158172 y
       have i₂ := eq158637 X0 y
       grind)
    | exact superpose eq158637 eq158172
    | exact resolve eq158172 eq158637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158172 eq158637
  have eq162902 : ∀ X0 : G, y = (M.op y X0) ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq162274 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162274
  have eq164171 : (M.op x y) = (τ (M.op (σ x) y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq94565 y
       have i₂ := eq162902 y
       grind)
    | exact superpose eq162902 eq94565
    | exact resolve eq94565 eq162902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94565 eq162902
  have eq164475 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    first
    | exact superpose eq152419 eq164171
    | exact resolve eq164171 eq152419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164171
  have eq164601 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    first
    | (have i₁ := eq164475
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq164475
    | exact resolve eq164475 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164475
  have eq164761 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq164601 eq15
    | exact resolve eq15 eq164601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164601
  have eq164833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq21 eq164761
    | exact resolve eq164761 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164761
  have eq164838 : x = (σ x) := by
    first
    | (have r₁ := eq164833
       have r₂ := eq28
       grind)
    | exact resolve eq164833 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164833
  have eq164940 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq164838 eq152419
    | exact resolve eq152419 eq164838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152419
  have eq164946 : (M.op (σ x) (σ y)) = (k y x) := by
    first
    | exact superpose eq164838 eq158263
    | exact resolve eq158263 eq164838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158263 eq164838
  have eq164950 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq164946
       have i₂ := eq158328
       grind)
    | exact superpose eq158328 eq164946
    | exact resolve eq164946 eq158328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158328 eq164946
  have eq164952 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq164940
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq164940
    | exact resolve eq164940 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq164940
  have eq165072 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq164952 eq28
    | exact resolve eq28 eq164952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq165224 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq164952 eq164950
    | exact resolve eq164950 eq164952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164950 eq164952
  have eq165230 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq165224 eq15
    | exact resolve eq15 eq165224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165224
  have eq165312 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq165230
    | exact resolve eq165230 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq165230
  have eq165322 : False := by grind
  exact eq165322
