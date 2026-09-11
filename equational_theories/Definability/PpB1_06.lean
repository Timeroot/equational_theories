import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyx_pxx_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 (M.op X0 X0) X1
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
  have eq673 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (k y x) := by
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
  have eq681 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
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
  clear eq28
  have eq692 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq692 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq692 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq692 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq692 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq692 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq702 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (k X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2 X0
       have i₂ := eq693 X0
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1190 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 X0 X1
       have i₂ := eq693 X0
       grind)
    | exact superpose eq693 eq702
    | exact resolve eq702 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq1411 : (k y y) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq693 y
       have i₂ := eq673
       grind)
    | exact superpose eq673 eq693
    | exact resolve eq693 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq1432 : (k x x) = (k y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1411
       have i₂ := eq693 x
       grind)
    | exact superpose eq693 eq1411
    | exact resolve eq1411 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq1449 : (k (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq681 eq693
    | exact resolve eq693 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq1470 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1449
       have i₂ := eq693 sF2
       grind)
    | exact superpose eq693 eq1449
    | exact resolve eq1449 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq5496 : ∀ X0 : G, y = (M.op (k x x) (M.op X0 (k x x))) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1190 y x
       have i₂ := eq1432
       grind)
    | exact superpose eq1432 eq1190
    | exact resolve eq1190 eq1432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq5497 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq5496 x
       have i₂ := eq1190 x x
       grind)
    | exact superpose eq1190 eq5496
    | exact resolve eq5496 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5496
  have eq5506 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq5497
       grind)
    | exact superpose eq5497 eq40
    | exact resolve eq40 eq5497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5497
  have eq5507 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq5506
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5506
    | exact resolve eq5506 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5506
  have eq5509 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq5507
    | exact resolve eq5507 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5507
  have eq6502 : ∀ X0 : G, (σ y) = (M.op (k (σ x) (σ x)) (M.op X0 (k (σ x) (σ x)))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq1470 eq1190
    | exact resolve eq1190 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq6503 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6502 x
       have i₂ := eq1190 sF2 x
       grind)
    | exact superpose eq1190 eq6502
    | exact resolve eq6502 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190 eq6502
  have eq6511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6503 eq5509
    | exact resolve eq5509 eq6503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5509 eq6503
  have eq6519 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq6511
       have r₂ := eq27
       grind)
    | exact resolve eq6511 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6511
  have eq6522 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq6519 eq32
    | exact resolve eq32 eq6519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq6519
  have eq6576 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq6522
    | exact resolve eq6522 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq6522
  have eq6577 : x = y := by grind
  clear eq6576
  have eq6584 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6577
       grind)
    | exact superpose eq6577 eq18
    | exact resolve eq18 eq6577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6585 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6577
       grind)
    | exact superpose eq6577 eq24
    | exact resolve eq24 eq6577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq6577
  have eq6619 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq6585
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6585
    | exact resolve eq6585 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6585
  have eq6620 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq6584
       have i₂ := eq693 x
       grind)
    | exact superpose eq693 eq6584
    | exact resolve eq6584 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6584
  have eq6624 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6619 eq26
    | exact resolve eq26 eq6619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6619
  have eq6676 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6624
       have i₂ := eq693 sF2
       grind)
    | exact superpose eq693 eq6624
    | exact resolve eq6624 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq6624
  have eq6685 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq6620
       grind)
    | exact superpose eq6620 eq40
    | exact resolve eq40 eq6620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq6620
  have eq6696 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6685
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6685
    | exact resolve eq6685 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6685
  have eq6701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6676 eq6696
    | exact resolve eq6696 eq6676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6676 eq6696
  have eq6704 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq6701
    | exact resolve eq6701 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6701
  have eq6706 : False := by grind
  exact eq6706

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_y_pxy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq43 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37
    | exact resolve eq37 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq44 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) X3) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X3 X4 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    grind
  have eq50 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq30
    | exact resolve eq30 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X1)) ≠ X0 ∨ (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op X2 (M.op X3 X0))) ∨ (k (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X1) (M.op X2 (M.op X3 X0))
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X0 X1) (M.op X2 (M.op X3 X0))
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq107 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq107
    | (have j0 := eq107 (σ X0)
       grind)
    | exact resolve eq107 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq123 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq44 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq44
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 X3 X4 X5 : G, (M.op X1 X0) = (M.op X1 (M.op X5 (M.op X3 (M.op X4 X0)))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq123 (M.op X3 (M.op X4 X0)) X1 (M.op X0 x) X5
       have i₂ := eq9 X0 x X3 X4
       grind)
    | exact superpose eq9 eq123
    | exact resolve eq123 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X2 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2
    grind
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X0) = (k (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 (M.op X2 (M.op x X0)) (M.op X0 X1)
       have i₂ := eq9 X0 X1 X2 x
       grind)
    | exact superpose eq9 eq47
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq254 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq254 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq254 X0 X1
       grind)
    | exact superpose eq254 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq254 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq254 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq254 X0 X1
       grind)
    | exact resolve eq13 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq685 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq673 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq686 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq685 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq693 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq686 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq686
    | (have j0 := eq686 X0 X1
       grind)
    | exact resolve eq686 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq694 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq693 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq1041 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) ≠ (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) ∨ (M.op (M.op X1 (M.op X2 (M.op X0 X3))) (M.op X1 (M.op X2 (M.op X0 X3)))) = X0 ∨ (M.op X0 X3) = (k X0 (M.op X1 (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq103 (M.op X0 X1) (M.op X2 (M.op X3 X0)) X2 X3
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | exact superpose eq9 eq103
    | (have r₁ := eq103 X0 (M.op X3 X0) X0 X3
       have r₂ := eq9 X0 (M.op X3 X0) X0 X3
       grind)
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq1063 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) ≠ (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) ∨ (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X3) = X0 ∨ (M.op X0 X3) = (k X0 (M.op X1 (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1041 X0 X1 X2 X3
       have i₂ := eq132 X3 (M.op X1 (M.op X2 (M.op X0 X3))) X2 X0 X1
       grind)
    | exact superpose eq132 eq1041
    | (have j0 := eq1041 X0 X1 X2 X3
       grind)
    | exact resolve eq1041 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1224 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq43
    | (have j1 := eq108 X0
       grind)
    | exact resolve eq43 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1228 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op X1 (M.op X2 (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1 X2
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq9
    | (have j1 := eq108 X0
       grind)
    | exact resolve eq9 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1248 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq108 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1254 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1224 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq1224
    | (have j0 := eq1224 X0
       grind)
    | exact resolve eq1224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1303 : ∀ X0 : G, (k (τ (σ X0)) X0) = X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq1254 X0
       grind)
    | exact superpose eq1254 eq43
    | (have j1 := eq1254 X0
       grind)
    | exact resolve eq43 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1306 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    grind
  clear eq1254
  have eq1325 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1306 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1306
    | (have j0 := eq1306 X0
       grind)
    | exact resolve eq1306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1328 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1303 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1303
    | (have j0 := eq1303 X0
       grind)
    | exact resolve eq1303 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303
  have eq1407 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 (τ (σ X0))) (τ (σ X0))) ∨ (σ (σ X0)) = (σ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0 (σ X0) (σ X0)
       have i₂ := eq1325 (σ X0)
       grind)
    | exact superpose eq1325 eq50
    | (have j1 := eq1325 (σ X0)
       grind)
    | exact resolve eq50 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1325
  have eq1429 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ (σ X0)) = (σ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1407 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1407
    | (have j0 := eq1407 X0
       grind)
    | exact resolve eq1407 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq1445 : ∀ X0 : G, (σ (σ X0)) = (σ (σ (k X0 X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1429 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1429
    | (have j0 := eq1429 X0
       grind)
    | exact resolve eq1429 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1861 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq694 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq694
    | exact resolve eq694 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1883 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq694 x y
       grind)
    | exact superpose eq694 eq16
    | (have j1 := eq694 x y
       grind)
    | exact resolve eq16 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1896 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (σ X0))) = (M.op (M.op (M.op X2 (M.op X3 (σ X0))) X4) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq45 (σ X0) X2 X3 X4 (σ X1)
       have i₂ := eq694 X1 X0
       grind)
    | exact superpose eq694 eq45
    | (have j1 := eq694 X1 X0
       grind)
    | exact resolve eq45 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq1903 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (σ X0))) = (M.op X2 (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq123 (σ X0) X2 X3 (σ X1)
       have i₂ := eq694 X1 X0
       grind)
    | exact superpose eq694 eq123
    | (have j1 := eq694 X1 X0
       grind)
    | exact resolve eq123 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1924 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1861 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1861
    | (have j0 := eq1861 X0 X1
       grind)
    | exact resolve eq1861 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1861
  have eq2038 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1924 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1924
    | exact resolve eq1924 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2057 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq1924 X0 X1
       grind)
    | exact superpose eq1924 eq30
    | (have j1 := eq1924 X0 X1
       grind)
    | exact resolve eq30 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924
  have eq2143 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq2038 (τ X1) X0
       grind)
    | exact superpose eq2038 eq18
    | (have j1 := eq2038 (τ X1) X0
       grind)
    | exact resolve eq18 eq2038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2195 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2057 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2057
    | exact resolve eq2057 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq2238 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2195 X0 X1
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq2195
    | (have j0 := eq2195 X0 X1
       grind)
    | exact resolve eq2195 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195
  have eq2285 : ∀ X0 X1 X2 : G, (τ (k X2 (k X1 X0))) = (k (τ X2) (τ (M.op X0 X1))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (k X1 X0) X2
       have i₂ := eq2238 X1 X0
       grind)
    | exact superpose eq2238 eq34
    | (have j1 := eq2238 X1 X0
       grind)
    | exact resolve eq34 eq2238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq2292 : ∀ X0 X1 X2 : G, (τ (k X2 (k X1 X0))) = (τ (k X2 (M.op X0 X1))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2285 X0 X1 X2
       have i₂ := eq34 (M.op X0 X1) X2
       grind)
    | exact superpose eq34 eq2285
    | (have j0 := eq2285 X0 X1 X2
       grind)
    | exact resolve eq2285 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2285
  have eq2424 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2143 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2143
    | exact resolve eq2143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143
  have eq2469 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2424 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2424
    | (have j0 := eq2424 X0 X1
       grind)
    | exact resolve eq2424 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424
  have eq2848 : ∀ X0 X1 : G, (τ (k (σ (σ X0)) X1)) = (k (σ (k X0 X0)) (τ X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ (k X0 X0)) X1
       have i₂ := eq1445 X0
       grind)
    | exact superpose eq1445 eq30
    | (have j1 := eq1445 X0
       grind)
    | exact resolve eq30 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq2870 : ∀ X0 X1 : G, (k (σ X0) (τ X1)) = (k (σ (k X0 X0)) (τ X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2848 X0 X1
       have i₂ := eq30 (σ X0) X1
       grind)
    | exact superpose eq30 eq2848
    | (have j0 := eq2848 X0 X1
       grind)
    | exact resolve eq2848 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2848
  have eq3469 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1883
       have i₂ := eq2038 y x
       grind)
    | exact superpose eq2038 eq1883
    | (have j1 := eq2038 (σ y) (σ x)
       grind)
    | exact resolve eq1883 eq2038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883
  have eq3474 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq3469
  have eq3475 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq3474
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq3474
    | (have j1 := eq694 x x
       grind)
    | exact resolve eq3474 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq3480 : x = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq43 x
       have i₂ := eq3474
       grind)
    | exact superpose eq3474 eq43
    | exact resolve eq43 eq3474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq3497 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq123 (σ x) X0 X1 (σ x)
       have i₂ := eq3474
       grind)
    | exact superpose eq3474 eq123
    | exact resolve eq123 eq3474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474
  have eq3515 : y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq3480
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3480
    | exact resolve eq3480 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3480
  have eq3517 : x = (k y x) ∨ x = (k y x) := by grind
  clear eq3515
  have eq3545 : x = (k y x) := by grind
  clear eq3517
  have eq3549 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2469 y x
       have i₂ := eq3545
       grind)
    | exact superpose eq3545 eq2469
    | (have j0 := eq2469 y x
       grind)
    | exact resolve eq2469 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469
  have eq3584 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ x))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (M.op x y)
       have i₂ := eq3549
       grind)
    | exact superpose eq3549 eq23
    | exact resolve eq23 eq3549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3606 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (k (τ X0) x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq3584 X0
       have i₂ := eq23 X0 x
       grind)
    | exact superpose eq23 eq3584
    | exact resolve eq3584 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3584
  have eq4516 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq3606 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3606
    | exact resolve eq3606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3606
  have eq4553 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op x y) (M.op X0 y)) x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq4516 (M.op (M.op x y) (M.op X0 y))
       have i₂ := eq156 x y X0
       grind)
    | exact superpose eq156 eq4516
    | exact resolve eq4516 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq4516
  have eq6344 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op (M.op X4 (M.op X5 (M.op X0 (M.op X1 X2)))) X0) ∨ (M.op (M.op X4 (M.op X5 (M.op X0 (M.op X1 X2)))) (M.op X3 X2)) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X4 (M.op X5 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1063 X1 X1 X2 (M.op X2 X0)
       have i₂ := eq123 X0 X1 X2 X3
       grind)
    | (have i₁ := eq1063 X1 X1 X2 (M.op X3 X0)
       have i₂ := eq123 X0 X1 X2 X3
       grind)
    | exact superpose eq123 eq1063
    | (have j0 := eq1063 X0 X4 X5 (M.op X1 X2)
       grind)
    | exact resolve eq1063 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq6430 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op (M.op X4 X2) X0) ∨ (M.op (M.op X4 (M.op X5 (M.op X0 (M.op X1 X2)))) (M.op X3 X2)) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X4 (M.op X5 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq6344 X0 X1 X2 X3 X4 X5
       have i₂ := eq132 X2 X4 X0 X1 X5
       grind)
    | exact superpose eq132 eq6344
    | (have j0 := eq6344 X0 X1 X2 X3 X4 X5
       grind)
    | exact resolve eq6344 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6344
  have eq6439 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op X3 X2)) = X0 ∨ (M.op X0 (M.op X1 X2)) ≠ (M.op (M.op X4 X2) X0) ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X4 (M.op X5 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq6430 X0 X1 X2 X3 X4 X5
       have i₂ := eq132 X2 X4 X0 X1 X5
       grind)
    | exact superpose eq132 eq6430
    | (have j0 := eq6430 X0 X1 X2 X3 X4 X5
       grind)
    | exact resolve eq6430 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6430
  have eq6448 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op (M.op X4 X2) X0) ∨ (M.op (M.op X4 X2) (M.op X3 X2)) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6439 X0 X1 X2 X3 X4 x
       have i₂ := eq132 X2 X4 X0 X1 x
       grind)
    | exact superpose eq132 eq6439
    | (have j0 := eq6439 X0 X1 X2 X3 X4 x
       grind)
    | exact resolve eq6439 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6439
  have eq14175 : ∀ X0 X1 X2 : G, (k X0 (k X2 X1)) = (σ (τ (k X0 (M.op X1 X2)))) ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (k X2 X1))
       have i₂ := eq2292 X1 X2 X0
       grind)
    | exact superpose eq2292 eq11
    | (have j1 := eq2292 X1 X2 X2
       grind)
    | exact resolve eq11 eq2292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2292
  have eq14213 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (k X0 (k X2 X1)) ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14175 X0 X1 X2
       have i₂ := eq11 (k X0 (M.op X1 X2))
       grind)
    | exact superpose eq11 eq14175
    | (have j0 := eq14175 X0 X1 X2
       grind)
    | exact resolve eq14175 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14175
  have eq52403 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (τ (k X0 X1)))) = (M.op X2 (M.op X3 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1903 (τ X0) (τ X1) X2 X3
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq1903
    | (have j0 := eq1903 (τ X0) (τ X1) X2 X3
       grind)
    | exact resolve eq1903 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq52797 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52403 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52403
    | (have j0 := eq52403 X0 X1 X2 X3
       grind)
    | exact resolve eq52403 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52403
  have eq52852 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X2 (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52797 X0 X1 X2 X3
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq52797
    | (have j0 := eq52797 X0 X1 X2 X3
       grind)
    | exact resolve eq52797 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52797
  have eq52886 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X2 (M.op X3 X0)) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52852 X0 X0 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52852
    | (have j0 := eq52852 X0 X1 X2 X3
       grind)
    | exact resolve eq52852 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52852
  have eq52894 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X2 (k X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52886 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52886
    | (have j0 := eq52886 X0 X1 X2 X3
       grind)
    | exact resolve eq52886 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52886
  have eq53118 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq52894 y x X0 X1
       have i₂ := eq3545
       grind)
    | exact superpose eq3545 eq52894
    | (have j0 := eq52894 y x x x
       grind)
    | exact resolve eq52894 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53130 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op X3 (M.op X4 (M.op X0 (k X1 X2)))) ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq44 X3 X1 X4 X0
       have i₂ := eq52894 X1 X2 X0 X3
       grind)
    | exact superpose eq52894 eq44
    | (have j1 := eq52894 X1 X2 X2 X3
       grind)
    | exact resolve eq44 eq52894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53329 : ∀ X0 X1 X2 X3 X4 X5 : G, (k X2 X3) = (M.op (M.op (k X2 X3) X4) (M.op X5 (M.op X0 (M.op X1 X2)))) ∨ (M.op X3 X3) = X2 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq9 (k X2 X3) X4 X5 X0
       have i₂ := eq52894 X2 X3 X0 X1
       grind)
    | exact superpose eq52894 eq9
    | (have j1 := eq52894 X2 X3 X2 X3
       grind)
    | exact resolve eq9 eq52894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52894
  have eq53443 : ∀ X2 X3 X4 : G, (k X2 X3) = (M.op (M.op (k X2 X3) X4) X2) ∨ (M.op X3 X3) = X2 := by
    intro X2 X3 X4
    first
    | (have i₁ := eq53329 x x X2 X3 X4 x
       have i₂ := eq132 X2 (M.op (k X2 X3) X4) x x x
       grind)
    | exact superpose eq132 eq53329
    | (have j0 := eq53329 x x X2 X3 X4 x
       grind)
    | exact resolve eq53329 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq53329
  have eq53493 : ∀ X0 X1 : G, y = (M.op (M.op y X1) (M.op X0 x)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y X1 X0 x
       have i₂ := eq53118 X0 x
       grind)
    | exact superpose eq53118 eq9
    | exact resolve eq9 eq53118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53611 : (M.op x y) = (k (M.op (M.op x y) x) x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4553 x
       have i₂ := eq53118 (M.op x y) x
       grind)
    | exact superpose eq53118 eq4553
    | exact resolve eq4553 eq53118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4553
  have eq53631 : (M.op x y) = (k (M.op (M.op x y) x) x) ∨ y = (M.op x x) := by grind
  clear eq53611
  have eq80837 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (σ (τ X0)))) = (M.op (M.op (M.op X2 (M.op X3 (σ (τ X0)))) X4) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1896 (τ X0) (τ X1) X2 X3 X4
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq1896
    | (have j0 := eq1896 (τ X0) (τ X1) X2 X3 X4
       grind)
    | exact resolve eq1896 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1896
  have eq81092 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (σ (τ X0)))) = (M.op (M.op (M.op X2 (M.op X3 (σ (τ X0)))) X4) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq80837 X0 X1 X2 X3 X4
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq80837
    | (have j0 := eq80837 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq80837 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80837
  have eq81142 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op X2 (M.op X3 X0)) X4) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq81092 X0 X1 X2 X3 X4
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81092
    | (have j0 := eq81092 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq81092 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81092
  have eq81177 : ∀ X0 X1 X2 X3 X4 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op X2 (M.op X3 X0)) X4) (k X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq81142 X0 X0 X2 X3 X4
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81142
    | (have j0 := eq81142 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq81142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81142
  have eq81186 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op X2 (M.op X3 X0)) X4) (k X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq81177 X0 X1 X2 X3 X4
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81177
    | (have j0 := eq81177 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq81177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81177
  have eq98702 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6448 (M.op X0 X1) X0 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6448
  have eq127738 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq3475
  have eq127827 : (σ y) = (σ (k x x)) ∨ y = (M.op x x) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq127738
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq127738
    | exact resolve eq127738 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127738
  have eq189386 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq127827
       grind)
    | exact superpose eq127827 eq10
    | exact resolve eq10 eq127827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127827
  have eq189544 : (σ x) = (σ (k x x)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq189386
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq189386
    | exact resolve eq189386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189386
  have eq189586 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1248 x
       have i₂ := eq189544
       grind)
    | exact superpose eq189544 eq1248
    | (have j0 := eq1248 x
       grind)
    | (have r₁ := eq1248 x
       have r₂ := eq189544
       grind)
    | exact resolve eq1248 eq189544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248 eq189544
  have eq189733 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by grind
  clear eq189586
  have eq189795 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq3497 X0 (σ x)
       have i₂ := eq189733
       grind)
    | exact superpose eq189733 eq3497
    | exact resolve eq3497 eq189733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3497
  have eq189915 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq189795 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189795
  have eq192406 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq189915 (σ x)
       grind)
    | exact superpose eq189915 eq16
    | exact resolve eq16 eq189915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189915
  have eq345793 : ∀ X0 X1 : G, (k (σ X1) X0) = (k (σ (k X1 X1)) X0) ∨ (k (k X1 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2870 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2870
    | (have j0 := eq2870 X1 X1
       grind)
    | exact resolve eq2870 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2870
  have eq347000 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X1))) = (k (τ (σ (k X0 X0))) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ (k X0 X0)) X1
       have i₂ := eq345793 (σ X1) X0
       grind)
    | exact superpose eq345793 eq23
    | (have j1 := eq345793 X0 X0
       grind)
    | exact resolve eq23 eq345793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345793
  have eq347185 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X1))) = (k (k X0 X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq347000 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq347000
    | (have j0 := eq347000 X0 X1
       grind)
    | exact resolve eq347000 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347000
  have eq347516 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (k (k X0 X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq347185 X0 X1
       have i₂ := eq23 (σ X0) X1
       grind)
    | exact superpose eq23 eq347185
    | (have j0 := eq347185 X0 X1
       grind)
    | exact resolve eq347185 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq347185
  have eq347740 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq347516 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq347516
    | (have j0 := eq347516 X0 X1
       grind)
    | exact resolve eq347516 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347516
  have eq348847 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq347740 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347740
  have eq348853 : ∀ X0 : G, (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq348847 X0
       have j1 := eq1328 X0
       grind)
    | (have r₁ := eq348847 X0
       have r₂ := eq1328 X0
       grind)
    | exact resolve eq348847 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328 eq348847
  have eq349324 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq348853 X0
       have i₂ := eq2038 (k X0 X0) X0
       grind)
    | exact superpose eq2038 eq348853
    | (have j1 := eq2038 X0 X0
       grind)
    | exact resolve eq348853 eq2038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038
  have eq349450 : ∀ X0 X1 : G, (k X1 X0) = (k X1 (M.op X0 (k X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14213 X1 X0 (k X0 X0)
       have i₂ := eq348853 X0
       grind)
    | exact superpose eq348853 eq14213
    | (have j0 := eq14213 X0 X0 (k X0 X0)
       grind)
    | exact resolve eq14213 eq348853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14213
  have eq349458 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op X3 X0))) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53130 X3 (k X0 X0) X0 X1 X2
       have i₂ := eq348853 X0
       grind)
    | exact superpose eq348853 eq53130
    | (have j0 := eq53130 X0 (k X0 X0) X0 X3 x
       grind)
    | exact resolve eq53130 eq348853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53130
  have eq349462 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53443 (k X0 X0) X0 x
       have i₂ := eq348853 X0
       grind)
    | exact superpose eq348853 eq53443
    | (have j0 := eq53443 (k X0 X0) X0 x
       grind)
    | exact resolve eq53443 eq348853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53443 eq348853
  have eq467446 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op X0 (M.op X1 y)) X2) x) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81186 y x X0 X1 X2
       have i₂ := eq3545
       grind)
    | exact superpose eq3545 eq81186
    | (have j0 := eq81186 y x X2 x x
       grind)
    | exact resolve eq81186 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3545 eq81186
  have eq588406 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) ∨ y = (k x x) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq192406
       have i₂ := eq189733
       grind)
    | exact superpose eq189733 eq192406
    | exact resolve eq192406 eq189733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189733 eq192406
  have eq588415 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) ∨ y = (k x x) := by grind
  clear eq588406
  have eq588420 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq588415
       have r₂ := eq3549
       grind)
    | exact resolve eq588415 eq3549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3549 eq588415
  have eq1001057 : ∀ X0 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 (M.op X2 (k X0 X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq98702 (M.op X0 x) (k X0 X0) X2
       have i₂ := eq349462 X0 x
       grind)
    | exact superpose eq349462 eq98702
    | (have j1 := eq349462 X0 x
       grind)
    | exact resolve eq98702 eq349462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98702 eq349462
  have eq1001854 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (k X0 X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have j0 := eq1001057 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001057
  have eq1002202 : ∀ X0 : G, x = (M.op x (M.op X0 y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1001854 x x
       have i₂ := eq588420
       grind)
    | exact superpose eq588420 eq1001854
    | exact resolve eq1001854 eq588420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1002311 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X1 (k X0 X0) X2 X0
       have i₂ := eq1001854 X0 X1
       grind)
    | exact superpose eq1001854 eq44
    | (have j1 := eq1001854 X0 X2
       grind)
    | exact resolve eq44 eq1001854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001854
  have eq1002838 : ∀ X0 : G, x = (M.op x (M.op X0 y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1002202 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002202
  have eq1015626 : ∀ X1 : G, x = (M.op (M.op x X1) x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq467446 x x x
       have i₂ := eq1002838 x
       grind)
    | exact superpose eq1002838 eq467446
    | exact resolve eq467446 eq1002838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467446
  have eq1015630 : ∀ X0 : G, y = (M.op (M.op y X0) x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x x
       have i₂ := eq1002838 x
       grind)
    | exact superpose eq1002838 eq9
    | exact resolve eq9 eq1002838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002838
  have eq1015940 : ∀ X1 : G, x = (M.op (M.op x X1) x) ∨ y = (M.op x x) := by
    intro X1
    first
    | (have j0 := eq1015626 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015626
  have eq1017739 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq53493 (M.op y x) X0
       have i₂ := eq1015630 x
       grind)
    | exact superpose eq1015630 eq53493
    | exact resolve eq53493 eq1015630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53493 eq1015630
  have eq1018092 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1017739 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017739
  have eq1018318 : (M.op x y) = (k x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq53631
       have i₂ := eq1015940 y
       grind)
    | exact superpose eq1015940 eq53631
    | exact resolve eq53631 eq1015940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53631 eq1015940
  have eq1018765 : (M.op x y) = (k x x) ∨ y = (M.op x x) := by grind
  clear eq1018318
  have eq1038437 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq53118 X0 (M.op y x)
       have i₂ := eq1018092 x
       grind)
    | exact superpose eq1018092 eq53118
    | exact resolve eq53118 eq1018092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53118 eq1018092
  have eq1038782 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1038437 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038437
  have eq1039666 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq588420
       have i₂ := eq1018765
       grind)
    | exact superpose eq1018765 eq588420
    | exact resolve eq588420 eq1018765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588420 eq1018765
  have eq1040127 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1039666
  have eq1056720 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1040127
       have i₂ := eq1038782 x
       grind)
    | exact superpose eq1038782 eq1040127
    | exact resolve eq1040127 eq1038782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038782 eq1040127
  have eq1056789 : y = (M.op x x) := by grind
  clear eq1056720
  have eq1057335 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X0 X1 x
       have i₂ := eq1056789
       grind)
    | exact superpose eq1056789 eq9
    | exact resolve eq9 eq1056789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1057338 : ∀ X0 X1 : G, y = (M.op x (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 x x x x
       have i₂ := eq1056789
       grind)
    | exact superpose eq1056789 eq44
    | exact resolve eq44 eq1056789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1057349 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq123 x X0 X1 x
       have i₂ := eq1056789
       grind)
    | exact superpose eq1056789 eq123
    | exact resolve eq123 eq1056789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1914032 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq349324 X0
       have i₂ := eq1002311 X0 X0 X1
       grind)
    | exact superpose eq1002311 eq349324
    | (have j0 := eq349324 X0
       have j1 := eq1002311 X0 X1 x
       grind)
    | exact resolve eq349324 eq1002311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349324 eq1002311
  have eq1914841 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1914032 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914032
  have eq1917402 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq180 X0 X0 x
       have i₂ := eq1914841 X0 x
       grind)
    | exact superpose eq1914841 eq180
    | (have j1 := eq1914841 X0 x
       grind)
    | exact resolve eq180 eq1914841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1917495 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq349458 X0 X1 X0 x
       have i₂ := eq1914841 X0 x
       grind)
    | exact superpose eq1914841 eq349458
    | (have j0 := eq349458 X0 X1 x x
       have j1 := eq1914841 X0 X1
       grind)
    | exact resolve eq349458 eq1914841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349458 eq1914841
  have eq1918290 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1917495 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917495
  have eq1957059 : ∀ X0 X1 : G, (k X1 X0) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq349450 X0 X1
       have i₂ := eq1918290 X0 X0
       grind)
    | exact superpose eq1918290 eq349450
    | (have j0 := eq349450 X0 X1
       have j1 := eq1918290 X0 X1
       grind)
    | exact resolve eq349450 eq1918290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349450 eq1918290
  have eq1957866 : ∀ X0 X1 : G, (k X1 X0) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1957059 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957059
  have eq1970399 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1917402 X0
       have i₂ := eq1957866 X0 X0
       grind)
    | exact superpose eq1957866 eq1917402
    | (have j0 := eq1917402 X0
       have j1 := eq1957866 X0 x
       grind)
    | exact resolve eq1917402 eq1957866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917402 eq1957866
  have eq1971558 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1970399 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970399
  have eq1973639 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1971558 (σ X0)
       grind)
    | exact superpose eq1971558 eq15
    | exact resolve eq15 eq1971558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1975176 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1973639 X0
       have i₂ := eq1971558 X0
       grind)
    | exact superpose eq1971558 eq1973639
    | exact resolve eq1973639 eq1971558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973639
  have eq1979113 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq123 (σ X0) X1 X2 (σ X0)
       have i₂ := eq1975176 X0
       grind)
    | exact superpose eq1975176 eq123
    | exact resolve eq123 eq1975176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq1992589 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1979113 (M.op x y) X0 X1
       have i₂ := eq1057335 y x
       grind)
    | exact superpose eq1057335 eq1979113
    | exact resolve eq1979113 eq1057335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1992682 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1979113 x X0 X1
       have i₂ := eq1056789
       grind)
    | exact superpose eq1056789 eq1979113
    | exact resolve eq1979113 eq1056789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056789 eq1979113
  have eq2012096 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (k (M.op x y) (M.op x y))) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1228 (M.op x y) X0 x
       have i₂ := eq1992589 X0 x
       grind)
    | exact superpose eq1992589 eq1228
    | (have j0 := eq1228 (M.op x y) x x
       grind)
    | exact resolve eq1228 eq1992589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228 eq1992589
  have eq2013216 : (σ (M.op x y)) = (M.op (σ (k (M.op x y) (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2012096 x
       have i₂ := eq1992682 (σ (k (M.op x y) (M.op x y))) x
       grind)
    | exact superpose eq1992682 eq2012096
    | exact resolve eq2012096 eq1992682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992682 eq2012096
  have eq2013527 : (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2013216
       have i₂ := eq1971558 (M.op x y)
       grind)
    | exact superpose eq1971558 eq2013216
    | exact resolve eq2013216 eq1971558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971558 eq2013216
  have eq2013753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2013527
       have i₂ := eq1057335 y x
       grind)
    | exact superpose eq1057335 eq2013527
    | exact resolve eq2013527 eq1057335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013527
  have eq2013914 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2013753
       have r₂ := eq16
       grind)
    | exact resolve eq2013753 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013753
  have eq2014043 : (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2013914
       have i₂ := eq1975176 (M.op x y)
       grind)
    | exact superpose eq1975176 eq2013914
    | exact resolve eq2013914 eq1975176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013914
  have eq2014139 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2014043
       have i₂ := eq1057335 y x
       grind)
    | exact superpose eq1057335 eq2014043
    | exact resolve eq2014043 eq1057335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057335 eq2014043
  have eq2014239 : (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq2014139
       grind)
    | exact superpose eq2014139 eq10
    | exact resolve eq10 eq2014139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014139
  have eq2015473 : x = (M.op x y) := by
    first
    | (have i₁ := eq2014239
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2014239
    | exact resolve eq2014239 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014239
  have eq2016135 : ∀ X0 : G, y = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1057338 X0 x
       have i₂ := eq2015473
       grind)
    | exact superpose eq2015473 eq1057338
    | exact resolve eq1057338 eq2015473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057338
  have eq2016457 : y = (M.op x y) := by
    first
    | (have i₁ := eq2016135 x
       have i₂ := eq1057349 x x
       grind)
    | exact superpose eq1057349 eq2016135
    | exact resolve eq2016135 eq1057349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057349 eq2016135
  have eq2016585 : x = y := by
    first
    | (have i₁ := eq2016457
       have i₂ := eq2015473
       grind)
    | exact superpose eq2015473 eq2016457
    | exact resolve eq2016457 eq2015473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015473 eq2016457
  have eq2016709 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2016585
       grind)
    | exact superpose eq2016585 eq16
    | exact resolve eq16 eq2016585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2016585
  have eq2018429 : False := by grind
  exact eq2018429

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_x_pxy_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq18
  have eq30 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq66 : ∀ X0 X1 X2 X4 : G, (M.op X2 (M.op X1 X0)) = (M.op X2 (M.op X4 X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq30 X2 (M.op X1 X0) X4 (M.op X0 x)
       have i₂ := eq9 X0 x X2 X1
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq155 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq155 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq155
    | (have j0 := eq155 (σ X0) (σ X1)
       grind)
    | exact resolve eq155 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X0
       have i₂ := eq155 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq155 X0 (M.op X1 X1)
       grind)
    | exact superpose eq155 eq12
    | (have j0 := eq12 X2 X0
       have j1 := eq155 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq155 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq155 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1069 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq174 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq1091 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1069 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1092 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1091 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1100 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1092 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1092
    | exact resolve eq1092 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1101 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1092 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq1092
    | exact resolve eq1092 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq1106 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1101 X0
       have i₂ := eq1092 X0
       grind)
    | exact superpose eq1092 eq1101
    | exact resolve eq1101 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1107 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1100 X0
       have i₂ := eq1092 X0
       grind)
    | exact superpose eq1092 eq1100
    | exact resolve eq1100 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092 eq1100
  have eq1118 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X2 (M.op X1 (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X2 X1
       have i₂ := eq1106 X0
       grind)
    | exact superpose eq1106 eq9
    | exact resolve eq9 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1194 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X2) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X2 X1 (σ X0)
       have i₂ := eq1107 X0
       grind)
    | exact superpose eq1107 eq9
    | exact resolve eq9 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1344 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq161 X0 X1
       have i₂ := eq1107 X0
       grind)
    | exact superpose eq1107 eq161
    | (have j0 := eq161 X0 X1
       grind)
    | exact resolve eq161 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq1107
  have eq1483 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1118 X0 (τ X0) X1
       have i₂ := eq1106 X0
       grind)
    | exact superpose eq1106 eq1118
    | exact resolve eq1118 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106 eq1118
  have eq1673 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq1344 X0 X1
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq1344 X0 X1
       grind)
    | exact superpose eq1344 eq10
    | (have j1 := eq1344 X0 X1
       grind)
    | exact resolve eq10 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq1730 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1673 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1673
    | (have j0 := eq1673 X0 X1
       grind)
    | exact resolve eq1673 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq4276 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1730 x y
       grind)
    | exact superpose eq1730 eq16
    | (have j1 := eq1730 x y
       grind)
    | exact resolve eq16 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq4536 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4276
       have i₂ := eq155 x y
       grind)
    | exact superpose eq155 eq4276
    | (have j1 := eq155 x y
       grind)
    | exact resolve eq4276 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq4276
  have eq4538 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq4536
  have eq4539 : y = (M.op x x) := by grind
  clear eq4538
  have eq4557 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1194 x X1 X0
       have i₂ := eq4539
       grind)
    | exact superpose eq4539 eq1194
    | exact resolve eq1194 eq4539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq4573 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 x x X1 X0
       have i₂ := eq4539
       grind)
    | exact superpose eq4539 eq66
    | exact resolve eq66 eq4539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq4539
  have eq10135 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (τ (σ x)) (M.op X0 (τ (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq1483 (M.op (σ x) (σ y)) x
       have i₂ := eq4557 (σ y) (σ x)
       grind)
    | exact superpose eq4557 eq1483
    | exact resolve eq1483 eq4557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483 eq4557
  have eq10198 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq10135 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10135
    | exact resolve eq10135 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10135
  have eq10208 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10198 x
       have i₂ := eq4573 x x
       grind)
    | exact superpose eq4573 eq10198
    | exact resolve eq10198 eq4573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4573 eq10198
  have eq10216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq10208
       grind)
    | exact superpose eq10208 eq11
    | exact resolve eq11 eq10208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10208
  have eq10229 : False := by grind
  exact eq10229

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pyy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
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
  have eq50 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 X1 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq76 y x
       grind)
    | exact superpose eq76 eq73
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq73 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq106
    | exact resolve eq106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
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
  have eq118 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq118 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq118 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq118 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq124 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq119 sF2
       grind)
    | exact superpose eq119 eq49
    | exact resolve eq49 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq127 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq124
       have i₂ := eq119 x
       grind)
    | exact superpose eq119 eq124
    | exact resolve eq124 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq124
  have eq1120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq108 eq76
    | (have j0 := eq76 (σ x) (σ y)
       grind)
    | exact resolve eq76 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq108
  have eq1121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq1120
    | exact resolve eq1120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1124 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1121
       have r₂ := eq27
       grind)
    | exact resolve eq1121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq1126 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq1124
    | exact resolve eq1124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1128 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1126 eq54
    | exact resolve eq54 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1129 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1126 eq51
    | exact resolve eq51 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1126
  have eq1361 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f1361_14 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
      intro X0
      grind
    have f1361_15 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
      intro X0
      grind
    have f1361_24 : (σ y) ≠ (σ x) := by grind
    have f1361_26 : (M.op x y) ≠ (M.op y x) := by grind
    have f1361_28 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
      intro X0
      first
      | (have j0 := f1361_15 X0
         grind)
      | (have r₁ := f1361_15 X0
         have r₂ := f1361_26
         grind)
      | exact resolve f1361_15 f1361_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1361_29 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
      intro X0
      first
      | (have j0 := f1361_14 X0
         grind)
      | (have r₁ := f1361_14 X0
         have r₂ := f1361_26
         grind)
      | exact resolve f1361_14 f1361_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1361_90 : (σ y) = (σ x) := by
      first
      | (have i₁ := f1361_28 x
         have i₂ := f1361_29 x
         grind)
      | exact superpose f1361_29 f1361_28
      | exact resolve f1361_28 f1361_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1361_94 : False := by
      first
      | (have r₁ := f1361_90
         have r₂ := f1361_24
         grind)
      | exact resolve f1361_90 f1361_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f1361_94
  clear eq1128 eq1129
  have eq1381 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq1361
  have eq1383 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq1381
       grind)
    | exact superpose eq1381 eq53
    | exact resolve eq53 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1384 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq50 X0 y
       have i₂ := eq1381
       grind)
    | exact superpose eq1381 eq50
    | exact resolve eq50 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1381
  have eq1515 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f1515_14 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) := by
      intro X0
      grind
    have f1515_15 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) := by
      intro X0
      grind
    have f1515_24 : y ≠ x := by grind
    have f1515_26 : (σ x) ≠ (σ y) := by grind
    have f1515_28 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
      intro X0
      first
      | (have j0 := f1515_15 X0
         grind)
      | (have r₁ := f1515_15 X0
         have r₂ := f1515_26
         grind)
      | exact resolve f1515_15 f1515_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1515_29 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
      intro X0
      first
      | (have j0 := f1515_14 X0
         grind)
      | (have r₁ := f1515_14 X0
         have r₂ := f1515_26
         grind)
      | exact resolve f1515_14 f1515_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1515_59 : y = x := by
      first
      | (have i₁ := f1515_28 x
         have i₂ := f1515_29 x
         grind)
      | exact superpose f1515_29 f1515_28
      | exact resolve f1515_28 f1515_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1515_63 : False := by
      first
      | (have r₁ := f1515_59
         have r₂ := f1515_24
         grind)
      | exact resolve f1515_59 f1515_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f1515_63
  clear eq1383 eq1384
  have eq1535 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1515
  have eq1744 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1535 eq29
    | exact resolve eq29 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1535
  have eq1768 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq1744
    | exact resolve eq1744 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1744
  have eq1769 : x = y := by grind
  clear eq1768
  have eq1774 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1769
       grind)
    | exact superpose eq1769 eq18
    | exact resolve eq18 eq1769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1775 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1769
       grind)
    | exact superpose eq1769 eq24
    | exact resolve eq24 eq1769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1769
  have eq1800 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1775
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1775
    | exact resolve eq1775 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1775
  have eq1805 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1800 eq26
    | exact resolve eq26 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1800
  have eq1857 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1805 eq127
    | exact resolve eq127 eq1805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq1805
  have eq1879 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1857
       have i₂ := eq1774
       grind)
    | exact superpose eq1774 eq1857
    | exact resolve eq1857 eq1774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774 eq1857
  have eq1880 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1879 eq15
    | exact resolve eq15 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq1901 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1880
    | exact resolve eq1880 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1880
  have eq1906 : False := by grind
  exact eq1906

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_y_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq18
  have eq30 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq71 : ∀ X0 X1 X2 X4 : G, (M.op X2 (M.op X1 X0)) = (M.op X2 (M.op X4 X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq30 X2 (M.op X1 X0) X4 (M.op X0 x)
       have i₂ := eq9 X0 x X2 X1
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq126 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq126 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq126
    | (have j0 := eq126 (σ X0) (σ X1)
       grind)
    | exact resolve eq126 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq126 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq126 (M.op X1 X1) X1
       grind)
    | exact superpose eq126 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq126 X2 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq126 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq126 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq12 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq145 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq818 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq794 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq819 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq818 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq827 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq819 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq819
    | exact resolve eq819 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq819 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq819
    | exact resolve eq819 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq833 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq828 X0
       have i₂ := eq819 X0
       grind)
    | exact superpose eq819 eq828
    | exact resolve eq828 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq834 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq827 X0
       have i₂ := eq819 X0
       grind)
    | exact superpose eq819 eq827
    | exact resolve eq827 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819 eq827
  have eq845 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X2 (M.op X1 (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X2 X1
       have i₂ := eq833 X0
       grind)
    | exact superpose eq833 eq9
    | exact resolve eq9 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X2) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X2 X1 (σ X0)
       have i₂ := eq834 X0
       grind)
    | exact superpose eq834 eq9
    | exact resolve eq9 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1017 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq834 X1
       grind)
    | exact superpose eq834 eq131
    | (have j0 := eq131 X0 X1
       grind)
    | exact resolve eq131 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq834
  have eq1139 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq845 X0 (τ X0) X1
       have i₂ := eq833 X0
       grind)
    | exact superpose eq833 eq845
    | exact resolve eq845 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq845
  have eq1314 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1017 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1017 X0 X1
       grind)
    | exact superpose eq1017 eq10
    | (have j1 := eq1017 X0 X1
       grind)
    | exact resolve eq10 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1370 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1314 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1314
    | (have j0 := eq1314 X0 X1
       grind)
    | exact resolve eq1314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq2241 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1370 y x
       grind)
    | exact superpose eq1370 eq16
    | (have j1 := eq1370 y x
       grind)
    | exact resolve eq16 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq2280 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2241
       have i₂ := eq126 y x
       grind)
    | exact superpose eq126 eq2241
    | (have j1 := eq126 y x
       grind)
    | exact resolve eq2241 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq2241
  have eq2282 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq2280
  have eq2283 : y = (M.op x x) := by grind
  clear eq2282
  have eq2294 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq900 x X1 X0
       have i₂ := eq2283
       grind)
    | exact superpose eq2283 eq900
    | exact resolve eq900 eq2283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq2306 : ∀ X0 X1 : G, (M.op X1 (M.op X0 x)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq71 x x X1 X0
       have i₂ := eq2283
       grind)
    | exact superpose eq2283 eq71
    | exact resolve eq71 eq2283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq2283
  have eq5117 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (τ (σ x)) (M.op X0 (τ (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq1139 (M.op (σ x) (σ y)) x
       have i₂ := eq2294 (σ y) (σ x)
       grind)
    | exact superpose eq2294 eq1139
    | exact resolve eq1139 eq2294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139 eq2294
  have eq5154 : ∀ X0 : G, (M.op x (M.op X0 x)) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq5117 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5117
    | exact resolve eq5117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5117
  have eq5163 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5154 x
       have i₂ := eq2306 x x
       grind)
    | exact superpose eq2306 eq5154
    | exact resolve eq5154 eq2306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306 eq5154
  have eq5169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq5163
       grind)
    | exact superpose eq5163 eq11
    | exact resolve eq11 eq5163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5163
  have eq5179 : False := by grind
  exact eq5179

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation1473 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 (M.op X0 x) x
       have i₂ := eq14 X0 x x X1
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
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq84 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) ≠ X0 ∨ (M.op X1 (M.op X2 X0)) = (M.op X0 X3) ∨ (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (k (M.op X1 (M.op X2 X0)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X1 (M.op X2 X0)) (M.op X0 X3)
       have i₂ := eq14 X0 X3 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 (M.op X2 X0)) (M.op X0 X3)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq526 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op (M.op X0 X1) X2) = X1 ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X1) X2)
       have i₂ := eq59 X1 X0 X2
       grind)
    | exact superpose eq59 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) X2)
       have r₂ := eq59 X0 X0 X2
       grind)
    | exact resolve eq12 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq954 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq72
  have eq1001 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq954 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq1217 : ∀ X2 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) X2) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) X2)) := by
    intro X2
    first
    | exact superpose eq57 eq84
    | (have r₁ := eq84 (σ y) (σ y) (σ x) x
       have r₂ := eq57 (M.op (σ x) (σ y)) (σ y)
       grind)
    | exact resolve eq84 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq84
  have eq10305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq105 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10306 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq10305
    | exact resolve eq10305 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10305
  have eq10317 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq10306
       have r₂ := eq28
       grind)
    | exact resolve eq10306 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10306
  have eq10321 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq10317
    | exact resolve eq10317 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10317
  have eq10483 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq10321 eq1217
    | (have j0 := eq1217 X0
       grind)
    | (have r₁ := eq1217 x
       have r₂ := eq10321
       grind)
    | exact resolve eq1217 eq10321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217 eq10321
  have eq10510 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq10483 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10483
  have eq26145 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq54 eq10510
    | exact resolve eq10510 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq10510
  have eq26172 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq26145
  have eq26179 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq26172 eq105
    | exact resolve eq105 eq26172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq26172
  have eq26196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq26179
  have eq26200 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq26196
       have r₂ := eq28
       grind)
    | exact resolve eq26196 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26196
  have eq26203 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq26200
       grind)
    | exact superpose eq26200 eq96
    | exact resolve eq96 eq26200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26233 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ y = (M.op (M.op x y) X0) ∨ (M.op x y) = (k y (M.op (M.op x y) X0)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq526 y y x
       have i₂ := eq26200
       grind)
    | exact superpose eq26200 eq526
    | (have j0 := eq526 x y X0
       grind)
    | (have r₁ := eq526 x y x
       have r₂ := eq26200
       grind)
    | exact resolve eq526 eq26200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq26200
  have eq26249 : ∀ X0 : G, (M.op x y) = (k y (M.op (M.op x y) X0)) ∨ y = (M.op (M.op x y) X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq26233 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26233
  have eq26280 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq26203
    | exact resolve eq26203 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26203
  have eq43997 : (M.op x y) = (k y x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq53 eq26249
    | exact resolve eq26249 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq26249
  have eq44044 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq43997
  have eq44114 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1001 x y
       have i₂ := eq44044
       grind)
    | exact superpose eq44044 eq1001
    | (have j0 := eq1001 x y
       grind)
    | exact resolve eq1001 eq44044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq44044
  have eq44119 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44114
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq44114
    | exact resolve eq44114 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44114
  have eq44137 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq44119
    | exact resolve eq44119 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44119
  have eq44148 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq44137
       have r₂ := eq26280
       grind)
    | exact resolve eq44137 eq26280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44137
  have eq44156 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44148
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq44148
    | exact resolve eq44148 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq44148
  have eq44163 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44156
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq44156
    | exact resolve eq44156 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44156
  have eq44168 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44163
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44163
    | exact resolve eq44163 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44163
  have eq44173 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq44168
    | exact resolve eq44168 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44168
  have eq44178 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44173
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq44173
    | exact resolve eq44173 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44173
  have eq44183 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44178
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44178
    | exact resolve eq44178 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44178
  have eq44184 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq44183
  have eq44283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq44184 eq26280
    | exact resolve eq26280 eq44184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26280 eq44184
  have eq44383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq44283
  have eq44414 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq44383
       have r₂ := eq28
       grind)
    | exact resolve eq44383 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44383
  have eq44424 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq44414 eq30
    | exact resolve eq30 eq44414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq44414
  have eq44563 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq44424
    | exact resolve eq44424 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq44424
  have eq44564 : x = y := by grind
  clear eq44563
  have eq44583 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq44564
       grind)
    | exact superpose eq44564 eq19
    | exact resolve eq19 eq44564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq44584 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq44564
       grind)
    | exact superpose eq44564 eq25
    | exact resolve eq25 eq44564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq44564
  have eq44721 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq44584
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44584
    | exact resolve eq44584 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq44584
  have eq44740 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq44721 eq27
    | exact resolve eq27 eq44721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq44721
  have eq45027 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq44740 eq71
    | exact resolve eq71 eq44740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq44740
  have eq45087 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq45027
       have i₂ := eq44583
       grind)
    | exact superpose eq44583 eq45027
    | exact resolve eq45027 eq44583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44583 eq45027
  have eq45121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45087 eq15
    | exact resolve eq15 eq45087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45087
  have eq45200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq45121
    | exact resolve eq45121 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq45121
  have eq45221 : False := by grind
  exact eq45221

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_x_pyx_Equation1473 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) X3) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X3 X4 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x) x
       have i₂ := eq9 X0 x x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq32 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq32
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq68 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X2 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1 X2
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq10
    | exact resolve eq10 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq133 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (σ X0))) = (M.op (M.op (M.op X1 (M.op X2 (σ X0))) X3) (σ (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 (σ X0) X1 X2 X3 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq25
    | exact resolve eq25 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (τ X0) (τ X0) x
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq26
    | exact resolve eq26 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq177 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op (τ X0) X1) (M.op X2 (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X1 X2 (τ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq9
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq185 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq184
    | (have j0 := eq184 X0 X1
       grind)
    | exact resolve eq184 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq194 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq185 y x
       grind)
    | exact superpose eq185 eq16
    | (have j1 := eq185 y x
       grind)
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq298 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 (τ X0) X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq177
    | exact resolve eq177 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq308 : ∀ X0 X1 X2 X4 : G, (M.op (τ X0) (M.op X1 X2)) = (M.op (τ X0) (M.op X4 X2)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq25 X2 (τ X0) X1 (M.op x (τ (M.op X0 X0))) X4
       have i₂ := eq177 X0 (M.op X1 X2) x
       grind)
    | exact superpose eq177 eq25
    | exact resolve eq25 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq377 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq308 (σ X0) X1 X2 x
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq308
    | exact resolve eq308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq463 : ∀ X0 X1 X3 X4 X5 : G, (M.op X1 X0) = (M.op X1 (M.op X5 (M.op X3 (M.op X4 X0)))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq377 X1 (M.op X0 x) (M.op X3 (M.op X4 X0)) X5
       have i₂ := eq9 X0 x X3 X4
       grind)
    | exact superpose eq9 eq377
    | exact resolve eq377 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq1074 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq194
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq194
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq194
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq194
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq194 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq1075 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq1074
  have eq1304 : ∀ X0 X1 X2 : G, (σ (σ X0)) = (M.op (σ (σ (M.op X0 X0))) (M.op X1 (M.op X2 (σ (σ X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (σ X0) X1 X2
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq68
    | exact resolve eq68 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1450 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq298 X0 (M.op (τ (M.op (M.op X0 X0) (M.op X0 X0))) x)
       have i₂ := eq176 (M.op X0 X0) x
       grind)
    | exact superpose eq176 eq298
    | exact resolve eq298 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq298
  have eq3315 : ∀ X0 X1 X2 X3 : G, (σ (M.op X2 X2)) = (M.op (σ (M.op (M.op X2 X2) (M.op X2 X2))) (M.op X3 (M.op X0 (M.op X1 (σ X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq68 (M.op X2 X2) X3 (M.op (M.op X0 (M.op X1 (σ X2))) x)
       have i₂ := eq133 X2 X0 X1 x
       grind)
    | exact superpose eq133 eq68
    | exact resolve eq68 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq3346 : ∀ X2 : G, (σ (M.op X2 X2)) = (M.op (σ (M.op (M.op X2 X2) (M.op X2 X2))) (σ X2)) := by
    intro X2
    first
    | (have i₁ := eq3315 x x X2 x
       have i₂ := eq463 (σ X2) (σ (M.op (M.op X2 X2) (M.op X2 X2))) x x x
       grind)
    | exact superpose eq463 eq3315
    | exact resolve eq3315 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq3315
  have eq8434 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq3346 X0
       grind)
    | exact superpose eq3346 eq68
    | exact resolve eq68 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq11510 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1075
       grind)
    | exact superpose eq1075 eq16
    | exact resolve eq16 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq11511 : (M.op y y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq11510
       have r₂ := eq22 x
       grind)
    | exact resolve eq11510 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11510
  have eq34968 : ∀ X0 X1 : G, (σ (σ X0)) = (M.op (σ (σ (M.op X0 X0))) (M.op X1 (σ (M.op (σ X0) (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1304 X0 X1 (σ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))))
       have i₂ := eq3346 (σ X0)
       grind)
    | exact superpose eq3346 eq1304
    | exact resolve eq1304 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304 eq3346
  have eq35106 : ∀ X0 X1 : G, (σ (σ X0)) = (M.op (σ (σ (M.op X0 X0))) (M.op X1 (σ (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq34968 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq34968
    | exact resolve eq34968 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34968
  have eq227302 : ∀ X0 X1 : G, (σ (σ (M.op (τ X0) (τ (M.op X0 X0))))) = (M.op (σ (σ (τ X0))) (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq35106 (M.op (τ X0) (τ (M.op X0 X0))) X1
       have i₂ := eq177 X0 (τ (M.op X0 X0)) (τ X0)
       grind)
    | exact superpose eq177 eq35106
    | exact resolve eq35106 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq35106
  have eq227710 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (σ (σ (M.op (τ X0) (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq227302 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq227302
    | exact resolve eq227302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227302
  have eq259854 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ (M.op X0 X0)))) = (τ (M.op (σ X0) (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ (M.op (τ X0) (τ (M.op X0 X0))))
       have i₂ := eq227710 X0 X1
       grind)
    | exact superpose eq227710 eq10
    | exact resolve eq10 eq227710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227710
  have eq718236 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op X0 (σ (M.op x x)))) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq8434 y x
       have i₂ := eq11511
       grind)
    | exact superpose eq11511 eq8434
    | exact resolve eq8434 eq11511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11511
  have eq718465 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq718236 x
       have i₂ := eq8434 x x
       grind)
    | exact superpose eq8434 eq718236
    | exact resolve eq718236 eq8434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718236
  have eq718466 : (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq718465
  have eq718482 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq718466
       grind)
    | exact superpose eq718466 eq22
    | exact resolve eq22 eq718466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718466
  have eq719201 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq718482
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq718482
    | exact resolve eq718482 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718482
  have eq719202 : (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq719201
  have eq720419 : ∀ X0 : G, (σ (M.op (τ (M.op y y)) (τ (M.op (M.op y y) (M.op y y))))) = (τ (M.op (σ (M.op x x)) (M.op X0 (σ (M.op x x))))) := by
    intro X0
    first
    | (have i₁ := eq259854 (M.op y y) x
       have i₂ := eq719202
       grind)
    | exact superpose eq719202 eq259854
    | exact resolve eq259854 eq719202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259854 eq719202
  have eq720450 : (τ (σ x)) = (σ (M.op (τ (M.op y y)) (τ (M.op (M.op y y) (M.op y y))))) := by
    first
    | (have i₁ := eq720419 x
       have i₂ := eq8434 x x
       grind)
    | exact superpose eq8434 eq720419
    | exact resolve eq720419 eq8434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8434 eq720419
  have eq720594 : (σ (τ y)) = (τ (σ x)) := by
    first
    | (have i₁ := eq720450
       have i₂ := eq1450 y
       grind)
    | exact superpose eq1450 eq720450
    | exact resolve eq720450 eq1450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450 eq720450
  have eq720642 : x = (σ (τ y)) := by
    first
    | (have i₁ := eq720594
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq720594
    | exact resolve eq720594 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720594
  have eq720664 : x = y := by
    first
    | (have i₁ := eq720642
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq720642
    | exact resolve eq720642 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720642
  have eq720666 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq720664
       grind)
    | exact superpose eq720664 eq16
    | exact resolve eq16 eq720664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720664
  have eq720667 : False := by grind
  exact eq720667

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation1473 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq98 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq386 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq98 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq13
    | (have j0 := eq13 (k (σ X1) (σ X0)) (M.op (σ X0) (σ X1))
       have j1 := eq98 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq98 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq98 X0 X1
       grind)
    | exact resolve eq13 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq415 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq416 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq415 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq424 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq416 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq416
    | (have j0 := eq416 X0 X1
       grind)
    | exact resolve eq416 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq425 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq424 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq2095 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq425
    | exact resolve eq425 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2107 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq425 x y
       grind)
    | exact superpose eq425 eq16
    | (have j1 := eq425 x y
       grind)
    | exact resolve eq16 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq2152 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2095 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq2095
    | (have j0 := eq2095 X0 X1
       grind)
    | exact resolve eq2095 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2095
  have eq2157 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2152 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2152
    | exact resolve eq2152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2152
  have eq2327 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2107
       have i₂ := eq2157 x y
       grind)
    | exact superpose eq2157 eq2107
    | (have j1 := eq2157 (σ x) (σ y)
       grind)
    | (have r₁ := eq2107
       have r₂ := eq2157 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2107
       have r₂ := eq2157 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2107 eq2157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107 eq2157
  have eq2330 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2327
  have eq2401 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2330
       grind)
    | exact superpose eq2330 eq10
    | exact resolve eq10 eq2330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2330
  have eq2443 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2401
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2401
    | exact resolve eq2401 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401
  have eq2444 : x = y := by grind
  clear eq2443
  have eq2446 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2444
       grind)
    | exact superpose eq2444 eq16
    | exact resolve eq16 eq2444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2444
  have eq2447 : False := by grind
  exact eq2447
