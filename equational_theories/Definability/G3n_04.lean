import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = Y then m(Y,X) else if X = Y then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyy_pxx_y_x_y_pxy_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq16
    | exact resolve eq16 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq19
    | exact resolve eq19 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq20
    | exact resolve eq20 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq49 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq25
    | exact resolve eq25 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq77 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq49
    | exact resolve eq49 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq161 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq77
    | exact resolve eq77 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X1) ≠ (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq175 X1
       grind)
    | exact superpose eq175 eq177
    | (have j0 := eq177 X0 X1
       grind)
    | (have r₁ := eq177 X0 X0
       have r₂ := eq175 X0
       grind)
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq277 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq161 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq161
    | exact resolve eq161 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq558 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = (M.op y y) ∨ x = y ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq9
    | (have j1 := eq11 y x
       grind)
    | (have r₁ := eq9
       have r₂ := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq11 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq558
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq558
    | exact resolve eq558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq561 : x = (k y y) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq560
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq560
    | exact resolve eq560 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq562 : (M.op y y) = (k x x) ∨ x = (k y y) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq561
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq561
    | exact resolve eq561 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq563 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = (k y y) ∨ (k y y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq562
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq562
    | exact resolve eq562 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq564 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = (k y y) ∨ (k y y) = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq563
       have i₂ := eq11 (σ y) (σ x)
       grind)
    | exact superpose eq11 eq563
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq563
       have r₂ := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq563
       have r₂ := eq11 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq563
       have r₂ := eq11 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq565 : x = (k y y) ∨ (k y y) = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq564
  have eq566 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (k y y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq565
       have i₂ := eq175 (σ y)
       grind)
    | exact superpose eq175 eq565
    | exact resolve eq565 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq567 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (k y y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq566
       have i₂ := eq175 (σ x)
       grind)
    | exact superpose eq175 eq566
    | exact resolve eq566 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq568 : x = y ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq567
       have i₂ := eq175 (σ y)
       grind)
    | exact superpose eq175 eq567
    | exact resolve eq567 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq607 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq568
       grind)
    | exact superpose eq568 eq9
    | exact resolve eq9 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq608 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq607
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq607
    | exact resolve eq607 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq609 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq608
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq608
    | exact resolve eq608 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq610 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq609
       have i₂ := eq175 (σ x)
       grind)
    | exact superpose eq175 eq609
    | (have r₁ := eq609
       have r₂ := eq175 (σ x)
       grind)
    | exact resolve eq609 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq611 : x = (k y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq610
  have eq612 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq277 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq277
    | exact resolve eq277 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq689 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq611
       grind)
    | exact superpose eq611 eq10
    | exact resolve eq10 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq691 : (k y y) = (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq689
  have eq733 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq691
       grind)
    | exact superpose eq691 eq10
    | exact resolve eq10 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq735 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq733
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq733
    | exact resolve eq733 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq736 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq735
  have eq777 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19 y y
       have i₂ := eq736
       grind)
    | exact superpose eq736 eq19
    | exact resolve eq19 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq811 : (k y y) = (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq777
       have i₂ := eq19 x x
       grind)
    | exact superpose eq19 eq777
    | exact resolve eq777 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq1298 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq612 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq612
    | exact resolve eq612 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq1586 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    grind
  have eq1587 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1586 X0
       have i₂ := eq175 (k X0 X0)
       grind)
    | exact superpose eq175 eq1586
    | (have j0 := eq1586 X0
       grind)
    | exact resolve eq1586 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586
  have eq2455 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ (k y y) ≠ (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq178 x y
       grind)
    | exact superpose eq178 eq9
    | (have j1 := eq178 x y
       grind)
    | exact resolve eq9 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2459 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k y y) ≠ (k x x) := by
    first
    | (have i₁ := eq2455
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq2455
    | exact resolve eq2455 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2455
  have eq2478 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k y y) ≠ (k x x) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2459
       have i₂ := eq178 (σ x) (σ y)
       grind)
    | exact superpose eq178 eq2459
    | (have j1 := eq178 x y
       grind)
    | (have r₁ := eq2459
       have r₂ := eq178 (σ x) (σ y)
       grind)
    | exact resolve eq2459 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2480 : (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k y y) ≠ (k x x) := by grind
  clear eq2478
  have eq2488 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k y y) ≠ (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2480
       have i₂ := eq736
       grind)
    | exact superpose eq736 eq2480
    | (have r₁ := eq2480
       have r₂ := eq736
       grind)
    | exact resolve eq2480 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq2489 : (k y y) ≠ (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq2488
  have eq2491 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq2489
       have r₂ := eq811
       grind)
    | exact resolve eq2489 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq2489
  have eq2493 : (σ x) ≠ (k (σ x) (σ x)) ∨ (k y y) ≠ (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2480
       have i₂ := eq2491
       grind)
    | exact superpose eq2491 eq2480
    | exact resolve eq2480 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480
  have eq2494 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19 y y
       have i₂ := eq2491
       grind)
    | exact superpose eq2491 eq19
    | exact resolve eq19 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2544 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2494
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq2494
    | exact resolve eq2494 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2494
  have eq4848 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1298 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1298
    | exact resolve eq1298 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq9664 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1587 (σ y)
       have i₂ := eq2491
       grind)
    | exact superpose eq2491 eq1587
    | exact resolve eq1587 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491
  have eq9740 : x = (k x x) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1587 y
       have i₂ := eq2544
       grind)
    | exact superpose eq2544 eq1587
    | exact resolve eq1587 eq2544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1587
  have eq9810 : (M.op x y) = (k y x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq9740
       grind)
    | exact superpose eq9740 eq10
    | exact resolve eq10 eq9740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9740
  have eq9816 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq9810
       grind)
    | exact superpose eq9810 eq9
    | exact resolve eq9 eq9810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9810
  have eq9819 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9816
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq9816
    | exact resolve eq9816 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9816
  have eq9821 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9819
       have r₂ := eq9664
       grind)
    | exact resolve eq9819 eq9664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9664 eq9819
  have eq9827 : (σ x) ≠ (σ x) ∨ (k y y) ≠ (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2493
       have i₂ := eq9821
       grind)
    | exact superpose eq9821 eq2493
    | (have r₁ := eq2493
       have r₂ := eq9821
       grind)
    | exact resolve eq2493 eq9821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2493
  have eq9867 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4848 x (σ x)
       have i₂ := eq9821
       grind)
    | exact superpose eq9821 eq4848
    | exact resolve eq4848 eq9821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4848 eq9821
  have eq9873 : (σ x) ≠ (σ x) ∨ (k y y) ≠ (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq9827
  have eq9874 : (k y y) ≠ (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq9873
  have eq9875 : x = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9867
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq9867
    | exact resolve eq9867 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9867
  have eq9914 : x ≠ (k x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2544 eq9874
    | exact resolve eq9874 eq2544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544 eq9874
  have eq9915 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq9914
       have r₂ := eq9875
       grind)
    | exact resolve eq9914 eq9875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9875 eq9914
  have eq9918 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k y y) ≠ (k x x) := by
    first
    | (have i₁ := eq2459
       have i₂ := eq9915
       grind)
    | exact superpose eq9915 eq2459
    | exact resolve eq2459 eq9915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2459
  have eq9921 : ∀ X0 : G, (τ (k (σ x) (σ X0))) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq19 y X0
       have i₂ := eq9915
       grind)
    | exact superpose eq9915 eq19
    | exact resolve eq19 eq9915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9922 : ∀ X0 : G, (τ (k (σ X0) (σ x))) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq19 X0 y
       have i₂ := eq9915
       grind)
    | exact superpose eq9915 eq19
    | exact resolve eq19 eq9915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9915
  have eq10010 : ∀ X0 : G, (k X0 x) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq9922 X0
       have i₂ := eq19 X0 x
       grind)
    | exact superpose eq19 eq9922
    | exact resolve eq9922 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9922
  have eq10011 : ∀ X0 : G, (k x X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq9921 X0
       have i₂ := eq19 x X0
       grind)
    | exact superpose eq19 eq9921
    | exact resolve eq9921 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq9921
  have eq10020 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k y y) ≠ (k x x) := by
    first
    | (have i₁ := eq9918
       have i₂ := eq175 (σ x)
       grind)
    | exact superpose eq175 eq9918
    | (have r₁ := eq9918
       have r₂ := eq175 (σ x)
       grind)
    | exact resolve eq9918 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq9918
  have eq10021 : (k y y) ≠ (k x x) := by grind
  clear eq10020
  have eq10032 : (k x x) ≠ (k x y) := by
    first
    | (have i₁ := eq10021
       have i₂ := eq10011 y
       grind)
    | exact superpose eq10011 eq10021
    | exact resolve eq10021 eq10011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10011 eq10021
  have eq10039 : (k x x) ≠ (k x x) := by
    first
    | (have i₁ := eq10032
       have i₂ := eq10010 x
       grind)
    | exact superpose eq10010 eq10032
    | (have r₁ := eq10032
       have r₂ := eq10010 x
       grind)
    | exact resolve eq10032 eq10010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10010 eq10032
  have eq10040 : False := by grind
  exact eq10040

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = Y then m(Y,X) else if X = Y then Y
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyy_pxx_y_x_y_pxy_pyx_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq51 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq52 (σ X0)
       grind)
    | exact superpose eq52 eq10
    | exact resolve eq10 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq52 x
       grind)
    | exact superpose eq52 eq45
    | exact resolve eq45 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq56 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq52 sF2
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq57 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq54 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq62 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq51
       have i₂ := eq52 sF2
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq52 x
       grind)
    | exact superpose eq52 eq73
    | exact resolve eq73 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq89 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (σ y) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq94 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq90
       have i₂ := eq52 sF3
       grind)
    | exact superpose eq52 eq90
    | exact resolve eq90 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq94
       have i₂ := eq52 y
       grind)
    | exact superpose eq52 eq94
    | exact resolve eq94 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq105 : (M.op x x) = (M.op y y) ∨ x = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq22 eq104
    | exact resolve eq104 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq116 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq16
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 X0 (τ X0)
       have i₂ := eq52 (τ X0)
       grind)
    | exact superpose eq52 eq36
    | exact resolve eq36 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq314 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq321 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq309 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq309
    | exact resolve eq309 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq322 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq321 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq321
    | exact resolve eq321 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq321
  have eq340 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq11 X1 (τ X0)
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 X1 (τ X0)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq521 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq522 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq521 X0
       have i₂ := eq10 X0 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq521
    | (have j0 := eq521 X0
       grind)
    | exact resolve eq521 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq533 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq524 X0
       have i₂ := eq57 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq524
    | (have j0 := eq524 X0
       grind)
    | exact resolve eq524 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq538 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq314 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq314
    | exact resolve eq314 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq664 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq322 X0
       grind)
    | exact superpose eq322 eq16
    | exact resolve eq16 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq848 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq664 X0
       grind)
    | exact superpose eq664 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3460 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq92
    | (have j0 := eq92 X0
       grind)
    | exact resolve eq92 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq3625 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3460 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3460
    | (have j0 := eq3460 x
       grind)
    | exact resolve eq3460 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3460
  have eq3628 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3625
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq3625
    | exact resolve eq3625 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3625
  have eq3646 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28 eq3628
    | exact resolve eq3628 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3628
  have eq3653 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3646
       have i₂ := eq56
       grind)
    | exact superpose eq56 eq3646
    | exact resolve eq3646 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3646
  have eq4754 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq340 X0 X1
       have i₂ := eq664 X0
       grind)
    | exact superpose eq664 eq340
    | (have j0 := eq340 X0 X1
       grind)
    | exact resolve eq340 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq4842 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4754 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq4754
    | (have j0 := eq4754 (σ X0) X1
       grind)
    | exact resolve eq4754 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4754
  have eq4916 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4842 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq4842
    | (have j0 := eq4842 X0 X1
       grind)
    | exact resolve eq4842 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4842
  have eq4921 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4916 X0 X1
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq4916
    | (have j0 := eq4916 X0 X1
       grind)
    | exact resolve eq4916 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4916
  have eq4922 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4921 X0 X1
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq4921
    | (have j0 := eq4921 X0 X1
       grind)
    | exact resolve eq4921 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4921
  have eq5825 : ∀ X0 : G, (k X0 (σ (τ (M.op X0 X0)))) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq311 X0
       have i₂ := eq664 X0
       grind)
    | exact superpose eq664 eq311
    | (have j0 := eq311 X0
       grind)
    | exact resolve eq311 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq5826 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5825 X0
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq5825
    | (have j0 := eq5825 X0
       grind)
    | exact resolve eq5825 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5825
  have eq5827 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5826 X0
       have i₂ := eq664 X0
       grind)
    | exact superpose eq664 eq5826
    | (have j0 := eq5826 X0
       grind)
    | exact resolve eq5826 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5826
  have eq5828 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (τ (M.op X0 X0)) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5827 X0
       have i₂ := eq664 (M.op X0 X0)
       grind)
    | exact superpose eq664 eq5827
    | (have j0 := eq5827 X0
       grind)
    | exact resolve eq5827 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5827
  have eq5922 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (τ (σ (M.op X0 X0))) (τ (σ X0)))) ∨ (τ (σ (M.op X0 X0))) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq5828 (σ X0)
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq5828
    | exact resolve eq5828 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5828
  have eq6034 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (τ (σ (M.op X0 X0))) X0)) ∨ (τ (σ (M.op X0 X0))) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq5922 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq5922
    | (have j0 := eq5922 X0
       grind)
    | exact resolve eq5922 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5922
  have eq6043 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) ∨ (τ (σ (M.op X0 X0))) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq6034 X0
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq6034
    | (have j0 := eq6034 X0
       grind)
    | exact resolve eq6034 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6034
  have eq6047 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) ∨ (τ (σ (M.op X0 X0))) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq6043 X0
       have i₂ := eq10 X0 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6043
    | (have j0 := eq6043 X0
       grind)
    | exact resolve eq6043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6043
  have eq6051 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (τ (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (σ (k X0 (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq6047 X0
       have i₂ := eq57 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq6047
    | (have j0 := eq6047 X0
       grind)
    | exact resolve eq6047 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6047
  have eq6055 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq6051 X0
       have i₂ := eq16 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq16 eq6051
    | (have j0 := eq6051 X0
       grind)
    | exact resolve eq6051 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6051
  have eq6059 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6055 X0
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq6055
    | (have j0 := eq6055 X0
       grind)
    | exact resolve eq6055 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6055
  have eq17433 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq522 X1 (σ X0)
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq522
    | (have j0 := eq522 X1 (σ X0)
       grind)
    | (have r₁ := eq522 X0 (σ X0)
       have r₂ := eq57 X0
       grind)
    | exact resolve eq522 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq522
  have eq17476 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17433 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq17433
    | (have j0 := eq17433 X0 X1
       grind)
    | exact resolve eq17433 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17433
  have eq367671 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X1 X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq848 X1 (τ X0)
       have i₂ := eq664 X0
       grind)
    | exact superpose eq664 eq848
    | (have j0 := eq848 X1 (τ X0)
       grind)
    | (have r₁ := eq848 X0 (τ X0)
       have r₂ := eq664 X0
       grind)
    | exact resolve eq848 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq848
  have eq367707 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq367671 X0 X1
       have i₂ := eq538 X1 X0
       grind)
    | exact superpose eq538 eq367671
    | (have j0 := eq367671 X0 X1
       grind)
    | exact resolve eq367671 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq367671
  have eq900064 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (σ (M.op X0 X0)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq17476 x X0
       have i₂ := eq56
       grind)
    | exact superpose eq56 eq17476
    | (have j0 := eq17476 x X0
       grind)
    | exact resolve eq17476 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900103 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (M.op (σ y) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq17476 X0 y
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq17476
    | (have j0 := eq17476 X0 y
       grind)
    | exact resolve eq17476 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17476
  have eq900108 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (M.op (σ y) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq900103 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq900103
    | (have j0 := eq900103 X0
       grind)
    | exact resolve eq900103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900103
  have eq900141 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (σ (M.op X0 X0)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq900064 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq900064
    | (have j0 := eq900064 X0
       grind)
    | exact resolve eq900064 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900064
  have eq900740 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq900141 y
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq900141
    | (have j0 := eq900141 x
       grind)
    | exact resolve eq900141 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq900800 : (σ (k x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq900740
       have r₂ := eq56
       grind)
    | exact resolve eq900740 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900740
  have eq900832 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq900800
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq900800
    | exact resolve eq900800 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900800
  have eq900837 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq900832
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq900832
    | exact resolve eq900832 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900832
  have eq900840 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq28 eq900837
    | exact resolve eq900837 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900837
  have eq900948 : ∀ X0 : G, (M.op x x) ≠ (τ (M.op X0 X0)) ∨ (τ (k (σ x) X0)) = (M.op (τ (σ x)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq74 eq367707
    | (have j0 := eq367707 (σ x) X0
       grind)
    | exact resolve eq367707 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900969 : ∀ X0 : G, (M.op y y) ≠ (τ (M.op X0 X0)) ∨ (τ (k X0 (σ y))) = (M.op (τ X0) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq116 eq367707
    | (have j0 := eq367707 X0 (σ y)
       grind)
    | exact resolve eq367707 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367707
  have eq900972 : ∀ X0 : G, (M.op y y) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq31 eq900969
    | (have j0 := eq900969 X0
       grind)
    | exact resolve eq900969 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900969
  have eq900990 : ∀ X0 : G, (M.op x x) ≠ (τ (M.op X0 X0)) ∨ (τ (k (σ x) X0)) = (M.op x (τ X0)) := by
    intro X0
    first
    | exact superpose eq30 eq900948
    | (have j0 := eq900948 X0
       grind)
    | exact resolve eq900948 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900948
  have eq901327 : (M.op x x) ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (k (σ x) (σ y))) = (M.op x (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3653 eq900990
    | (have j0 := eq900990 (σ x)
       grind)
    | exact resolve eq900990 eq3653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3653
  have eq901353 : (τ (k (σ x) (σ y))) = (M.op x (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq901327
       have r₂ := eq74
       grind)
    | exact resolve eq901327 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901327
  have eq901370 : (M.op x y) = (τ (k (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31 eq901353
    | exact resolve eq901353 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901353
  have eq901375 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq62 eq901370
    | exact resolve eq901370 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901370
  have eq901380 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq901375
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq901375
    | exact resolve eq901375 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901375
  have eq901464 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq901380 eq103
    | exact resolve eq103 eq901380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq901380
  have eq901874 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4922 x y
       have i₂ := eq901464
       grind)
    | exact superpose eq901464 eq4922
    | (have j0 := eq4922 x y
       grind)
    | exact resolve eq4922 eq901464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4922 eq901464
  have eq901877 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq901874
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq901874
    | exact resolve eq901874 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901874
  have eq901960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq901877
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq901877
    | exact resolve eq901877 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901877
  have eq902034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq901960
    | exact resolve eq901960 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901960
  have eq902036 : (M.op x x) = (M.op y y) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq902034
       have r₂ := eq29
       grind)
    | exact resolve eq902034 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902034
  have eq902038 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq902036
       grind)
    | exact superpose eq902036 eq96
    | exact resolve eq96 eq902036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902036
  have eq902355 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq902038
       have i₂ := eq56
       grind)
    | exact superpose eq56 eq902038
    | exact resolve eq902038 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902038
  have eq903091 : (M.op x x) ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (k (σ x) (σ y))) = (M.op x (τ (σ y))) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq902355 eq900990
    | (have j0 := eq900990 (σ x)
       grind)
    | exact resolve eq900990 eq902355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902355
  have eq903099 : (τ (k (σ x) (σ y))) = (M.op x (τ (σ y))) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq903091
       have r₂ := eq74
       grind)
    | exact resolve eq903091 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903091
  have eq903227 : (M.op x y) = (τ (k (σ x) (σ y))) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31 eq903099
    | exact resolve eq903099 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903099
  have eq903262 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq62 eq903227
    | exact resolve eq903227 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903227
  have eq903288 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq903262
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq903262
    | exact resolve eq903262 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903262
  have eq903289 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq903288
  have eq903323 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq903289 eq116
    | exact resolve eq116 eq903289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903289
  have eq903656 : x = (M.op y y) ∨ x = (M.op y y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq903323
    | exact resolve eq903323 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903323
  have eq903657 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq903656
  have eq903809 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq903657
       grind)
    | exact superpose eq903657 eq46
    | exact resolve eq46 eq903657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903657
  have eq903979 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq903809
    | exact resolve eq903809 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903809
  have eq904082 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq903979 eq900840
    | exact resolve eq900840 eq903979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900840
  have eq904093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq904082
  have eq904101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq904093
       have r₂ := eq29
       grind)
    | exact resolve eq904093 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904093
  have eq904291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq904101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq904101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904101
  have eq904292 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq904291
  have eq904297 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq904292
    | exact resolve eq904292 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904292
  have eq904382 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq904297
       have r₂ := eq29
       grind)
    | exact resolve eq904297 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904297
  have eq1054414 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq904382 eq116
    | exact resolve eq116 eq904382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904382
  have eq1054762 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq74 eq1054414
    | exact resolve eq1054414 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054414
  have eq1058429 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq900141 y
       have i₂ := eq1054762
       grind)
    | exact superpose eq1054762 eq900141
    | (have j0 := eq900141 x
       grind)
    | exact resolve eq900141 eq1054762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900141 eq1054762
  have eq1058455 : (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1058429
       have r₂ := eq56
       grind)
    | exact resolve eq1058429 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058429
  have eq1058605 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1058455
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1058455
    | exact resolve eq1058455 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058455
  have eq1058677 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1058605
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq1058605
    | exact resolve eq1058605 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058605
  have eq1058739 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq1058677
    | exact resolve eq1058677 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058677
  have eq1058966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq1058739 eq903979
    | exact resolve eq903979 eq1058739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903979 eq1058739
  have eq1059046 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1058966
  have eq1059056 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1059046
       have r₂ := eq29
       grind)
    | exact resolve eq1059046 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059046
  have eq1059063 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1059056 eq116
    | exact resolve eq116 eq1059056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1059056
  have eq1059418 : x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30 eq1059063
    | exact resolve eq1059063 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059063
  have eq1059419 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1059418
  have eq1059535 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq1059419
       grind)
    | exact superpose eq1059419 eq96
    | exact resolve eq96 eq1059419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1059619 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq533 y
       have i₂ := eq1059419
       grind)
    | exact superpose eq1059419 eq533
    | exact resolve eq533 eq1059419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq1059651 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6059 y
       have i₂ := eq1059419
       grind)
    | exact superpose eq1059419 eq6059
    | exact resolve eq6059 eq1059419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6059
  have eq1059800 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1059651
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq1059651
    | exact resolve eq1059651 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059651
  have eq1059808 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1059619
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq1059619
    | exact resolve eq1059619 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq1059619
  have eq1059890 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1059535
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1059535
    | exact resolve eq1059535 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059535
  have eq1059952 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1059800
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq1059800
    | exact resolve eq1059800 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059800
  have eq1059960 : (k (σ y) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1059808
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1059808
    | exact resolve eq1059808 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059808
  have eq1060036 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22 eq1059952
    | exact resolve eq1059952 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059952
  have eq1060043 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1059960
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1059960
    | exact resolve eq1059960 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059960
  have eq1060097 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq1060043
    | exact resolve eq1060043 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060043
  have eq1060128 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1060097
       have i₂ := eq56
       grind)
    | exact superpose eq56 eq1060097
    | exact resolve eq1060097 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1060097
  have eq1060155 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1060128
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1060128
    | exact resolve eq1060128 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060128
  have eq1060413 : (τ (σ x)) ≠ (M.op x x) ∨ (τ (k (σ x) (σ y))) = (M.op x (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1059890 eq900990
    | (have j0 := eq900990 (σ y)
       grind)
    | exact resolve eq900990 eq1059890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900990
  have eq1060432 : x ≠ (M.op x x) ∨ (τ (k (σ x) (σ y))) = (M.op x (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30 eq1060413
    | exact resolve eq1060413 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060413
  have eq1060563 : (M.op x y) = (τ (k (σ x) (σ y))) ∨ x ≠ (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31 eq1060432
    | exact resolve eq1060432 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060432
  have eq1060614 : (M.op x y) = (k x y) ∨ x ≠ (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq62 eq1060563
    | exact resolve eq1060563 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060563
  have eq1060640 : x ≠ (M.op x x) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1060614
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq1060614
    | exact resolve eq1060614 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060614
  have eq1066296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1060155 eq1060036
    | exact resolve eq1060036 eq1060155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060036 eq1060155
  have eq1066305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1066296
  have eq1066352 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1066305
       have r₂ := eq29
       grind)
    | exact resolve eq1066305 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066305
  have eq1066358 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq1066352 eq74
    | exact resolve eq74 eq1066352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1066557 : (τ (σ x)) ≠ (M.op y y) ∨ (τ (k (σ x) (σ y))) = (M.op (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq1066352 eq900972
    | (have j0 := eq900972 (σ x)
       grind)
    | exact resolve eq900972 eq1066352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900972 eq1066352
  have eq1066632 : x ≠ (M.op y y) ∨ (τ (k (σ x) (σ y))) = (M.op (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq1066557
    | exact resolve eq1066557 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066557
  have eq1066756 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq1066358
    | exact resolve eq1066358 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066358
  have eq1066757 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1066756
  have eq1066761 : (τ (k (σ x) (σ y))) = (M.op (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1066632
       have r₂ := eq1059419
       grind)
    | exact resolve eq1066632 eq1059419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059419 eq1066632
  have eq1066810 : (M.op x y) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq1066761
    | exact resolve eq1066761 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066761
  have eq1066826 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq62 eq1066810
    | exact resolve eq1066810 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1066810
  have eq1066836 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1066826
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq1066826
    | exact resolve eq1066826 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066826
  have eq1066837 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1066836
       have r₂ := eq1060640
       grind)
    | exact resolve eq1066836 eq1060640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060640 eq1066836
  have eq1067023 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq900108 x
       have i₂ := eq1066757
       grind)
    | exact superpose eq1066757 eq900108
    | (have j0 := eq900108 x
       grind)
    | exact resolve eq900108 eq1066757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900108 eq1066757
  have eq1067113 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1067023
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1067023
    | exact resolve eq1067023 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067023
  have eq1067282 : (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1067113
       have r₂ := eq1059890
       grind)
    | exact resolve eq1067113 eq1059890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059890 eq1067113
  have eq1067389 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1067282
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1067282
    | exact resolve eq1067282 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067282
  have eq1067456 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1067389
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq1067389
    | exact resolve eq1067389 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067389
  have eq1067496 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq1067456
    | exact resolve eq1067456 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067456
  have eq1067551 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46
       have i₂ := eq1066837
       grind)
    | exact superpose eq1066837 eq46
    | exact resolve eq46 eq1066837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq1066837
  have eq1067755 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22 eq1067551
    | exact resolve eq1067551 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067551
  have eq1069457 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1067755 eq1067496
    | exact resolve eq1067496 eq1067755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067496 eq1067755
  have eq1069466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1069457
  have eq1069495 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1069466
       have r₂ := eq29
       grind)
    | exact resolve eq1069466 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069466
  have eq1069594 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1069495 eq31
    | exact resolve eq31 eq1069495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1069495
  have eq1070729 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq1069594
    | exact resolve eq1069594 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1069594
  have eq1070730 : x = y := by grind
  clear eq1070729
  have eq1071845 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq1070730
       grind)
    | exact superpose eq1070730 eq20
    | exact resolve eq20 eq1070730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1071846 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq1070730
       grind)
    | exact superpose eq1070730 eq26
    | exact resolve eq26 eq1070730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1070730
  have eq1072962 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1071846
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1071846
    | exact resolve eq1071846 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1071846
  have eq1073134 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1072962 eq28
    | exact resolve eq28 eq1072962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1072962
  have eq1075623 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1073134 eq74
    | exact resolve eq74 eq1073134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1073134
  have eq1075985 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1075623
       have i₂ := eq1071845
       grind)
    | exact superpose eq1071845 eq1075623
    | exact resolve eq1075623 eq1071845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071845 eq1075623
  have eq1076263 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1075985 eq15
    | exact resolve eq15 eq1075985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075985
  have eq1077064 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq1076263
    | exact resolve eq1076263 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1076263
  have eq1077302 : False := by grind
  exact eq1077302

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else if m(X,Y) = m(Y,Y) then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyy_pxy_y_pxy_pyy_pxy_pyy_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq16
    | exact resolve eq16 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq18
    | exact resolve eq18 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (σ X0) (σ X1))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq21
    | exact resolve eq21 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq62 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq30
    | exact resolve eq30 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq110 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq62
    | exact resolve eq62 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) ≠ (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X1
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq176
    | (have j0 := eq176 X0 X1
       grind)
    | (have r₁ := eq176 X0 X0
       have r₂ := eq174 X0
       grind)
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq209 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq110
    | exact resolve eq110 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq424 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq209
    | exact resolve eq209 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq747 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq424 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq424
    | exact resolve eq424 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq424 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq424
    | exact resolve eq424 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq1200 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq17 x y
       grind)
    | exact superpose eq17 eq9
    | (have j1 := eq17 x y
       grind)
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1202 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq17 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1203 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq17 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1204 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1203 X0 X1
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq1203
    | (have j0 := eq1203 X0 X1
       grind)
    | exact resolve eq1203 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1205 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1202 X0 X1
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq1202
    | (have j0 := eq1202 X0 X1
       grind)
    | (have r₁ := eq1202 X0 X0
       have r₂ := eq174 X0
       grind)
    | exact resolve eq1202 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1207 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1200
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq1200
    | exact resolve eq1200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1208 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1205 X0 X1
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq1205
    | (have j0 := eq1205 X0 X1
       grind)
    | exact resolve eq1205 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1210 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1207
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1207
    | exact resolve eq1207 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1288 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1210
       have i₂ := eq17 (σ x) (σ y)
       grind)
    | exact superpose eq17 eq1210
    | (have j1 := eq17 (σ x) (σ y)
       grind)
    | (have r₁ := eq1210
       have r₂ := eq17 (σ x) (σ y)
       grind)
    | exact resolve eq1210 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1289 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1288
  have eq1290 : y = (M.op x y) ∨ (M.op x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1289
       have i₂ := eq174 (σ y)
       grind)
    | exact superpose eq174 eq1289
    | exact resolve eq1289 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq1368 : y ≠ y ∨ (M.op y y) = (M.op x x) ∨ (k x y) = (M.op y y) ∨ (M.op x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1290
       grind)
    | exact superpose eq1290 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1290
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1290
       grind)
    | exact resolve eq13 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1369 : y ≠ (k y y) ∨ (M.op x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq1370 : (M.op y y) = (M.op x x) ∨ (k x y) = (M.op y y) ∨ (M.op x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1368
  have eq1371 : (M.op y y) = (k x x) ∨ (k x y) = (M.op y y) ∨ (M.op x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1370
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1370
    | exact resolve eq1370 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1373 : (k y y) = (k x x) ∨ (k x y) = (M.op y y) ∨ (M.op x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1371
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1371
    | exact resolve eq1371 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq1374 : (k y y) = (k x x) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1373
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1373
    | exact resolve eq1373 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq1535 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1374
       grind)
    | exact superpose eq1374 eq10
    | exact resolve eq10 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1536 : (k x y) ≠ (k x x) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq1538 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1535
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1535
    | exact resolve eq1535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1624 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq747 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq747
    | exact resolve eq747 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq1711 : (σ y) ≠ (k (σ y) (σ y)) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1538
  have eq1718 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq763 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq763
    | exact resolve eq763 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq2239 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = (k X0 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2244 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2239 X0 X1
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq2239
    | (have j0 := eq2239 X0 X1
       grind)
    | (have r₁ := eq2239 X0 X0
       have r₂ := eq174 X0
       grind)
    | exact resolve eq2239 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239
  have eq2389 : y ≠ (k x y) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1204 x y
       grind)
    | exact superpose eq1204 eq9
    | (have j1 := eq1204 x y
       grind)
    | exact resolve eq9 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2394 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq1204 X1 X0
       grind)
    | exact superpose eq1204 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq1204 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq1204 X0 X1
       grind)
    | exact resolve eq13 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq2398 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2394 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2394
  have eq2399 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2398 X0 X1
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq2398
    | (have j0 := eq2398 X0 X1
       grind)
    | exact resolve eq2398 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2398
  have eq2402 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2399 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq2399
    | (have j0 := eq2399 X0 X1
       grind)
    | exact resolve eq2399 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399
  have eq2403 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (k X0 X0) = (k X1 X1) ∨ (k X1 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2402 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq2402
    | (have j0 := eq2402 X0 X1
       grind)
    | exact resolve eq2402 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2402
  have eq2926 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1624 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1624
    | exact resolve eq1624 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624
  have eq2996 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1718 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1718
    | exact resolve eq1718 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq3105 : (k x y) ≠ (k y y) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1208 x y
       grind)
    | exact superpose eq1208 eq9
    | (have j1 := eq1208 x y
       grind)
    | exact resolve eq9 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4556 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X1) ∨ (k X1 X0) = X0 ∨ (k X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X1 X0
       have i₂ := eq1208 X1 X0
       grind)
    | exact superpose eq1208 eq177
    | (have j0 := eq177 X0 X1
       have j1 := eq1208 X1 X0
       grind)
    | exact resolve eq177 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4560 : (k y y) ≠ (k x x) ∨ (k x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1290
       have i₂ := eq177 x y
       grind)
    | exact superpose eq177 eq1290
    | (have j1 := eq177 y x
       grind)
    | exact resolve eq1290 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq4561 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ (k y y) ≠ (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq177 x y
       grind)
    | exact superpose eq177 eq9
    | (have j1 := eq177 y x
       grind)
    | exact resolve eq9 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4570 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1210
       have i₂ := eq177 (σ x) (σ y)
       grind)
    | exact superpose eq177 eq1210
    | (have j1 := eq177 (σ y) (σ x)
       grind)
    | (have r₁ := eq1210
       have r₂ := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq1210 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq4571 : (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y y) := by grind
  clear eq4570
  have eq4581 : (k y y) ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq4561
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq4561
    | exact resolve eq4561 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4561
  have eq4735 : (k x x) ≠ (k x x) ∨ (k x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4560
       have i₂ := eq1374
       grind)
    | exact superpose eq1374 eq4560
    | (have r₁ := eq4560
       have r₂ := eq1374
       grind)
    | exact resolve eq4560 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374 eq4560
  have eq4736 : (k x x) ≠ (k x x) ∨ (k x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) := by grind
  clear eq4735
  have eq4737 : (k x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) := by grind
  clear eq4736
  have eq4738 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) := by
    first
    | (have r₁ := eq4737
       have r₂ := eq1536
       grind)
    | exact resolve eq4737 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4737
  have eq5040 : (k x y) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq4738
       grind)
    | exact superpose eq4738 eq10
    | exact resolve eq10 eq4738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4738
  have eq5516 : (σ (k x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq5040
       grind)
    | exact superpose eq5040 eq10
    | exact resolve eq10 eq5040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5040
  have eq5519 : (M.op x y) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq5516
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq5516
    | exact resolve eq5516 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5516
  have eq5849 : (k y y) ≠ (k x x) ∨ (k x y) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq5519
       grind)
    | exact superpose eq5519 eq177
    | (have j0 := eq177 y x
       grind)
    | exact resolve eq177 eq5519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6658 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2926 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2926
    | exact resolve eq2926 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926
  have eq7002 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2996 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2996
    | exact resolve eq2996 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996
  have eq11746 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6658 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq6658
    | exact resolve eq6658 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6658
  have eq12024 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7002 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq7002
    | exact resolve eq7002 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12090 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7002 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq7002
    | exact resolve eq7002 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7002
  have eq15191 : y = (k y y) ∨ (k y y) ≠ (k y y) ∨ (k y y) = (k x x) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2244 y x
       have i₂ := eq5519
       grind)
    | exact superpose eq5519 eq2244
    | (have j0 := eq2244 (σ y) (σ x)
       grind)
    | (have r₁ := eq2244 y x
       have r₂ := eq5519
       grind)
    | (have r₁ := eq2244 (σ y) (σ x)
       have r₂ := eq5519
       grind)
    | exact resolve eq2244 eq5519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5519
  have eq15194 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) ≠ (k y y) ∨ (k y y) = (k x x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq2244 y x
       grind)
    | exact superpose eq2244 eq9
    | (have j1 := eq2244 y x
       grind)
    | exact resolve eq9 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15195 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq2244 X0 X1
       grind)
    | exact superpose eq2244 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq2244 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq2244 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq2244 X0 X0
       grind)
    | exact resolve eq13 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15199 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15195 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15195
  have eq15202 : y = (k x y) ∨ (k y y) = (k x x) ∨ y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq15191
  have eq15205 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15199 X0 X1
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq15199
    | (have j0 := eq15199 X0 X1
       grind)
    | (have r₁ := eq15199 X0 X0
       have r₂ := eq174 X0
       grind)
    | exact resolve eq15199 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15199
  have eq15209 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15205 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq15205
    | (have j0 := eq15205 X0 X1
       grind)
    | (have r₁ := eq15205 X0 X0
       have r₂ := eq174 X0
       grind)
    | exact resolve eq15205 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15205
  have eq15210 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) ≠ (k X0 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15209 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15209
  have eq15211 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X1) ∨ (k X1 X0) = (k X0 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15210 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq15210
    | (have j0 := eq15210 X0 X1
       grind)
    | (have r₁ := eq15210 X0 X0
       have r₂ := eq174 X0
       grind)
    | exact resolve eq15210 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15210
  have eq18981 : (σ y) = (k (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq15202
       grind)
    | exact superpose eq15202 eq10
    | exact resolve eq10 eq15202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15202
  have eq18982 : y = (k y y) ∨ (k y y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq18981
  have eq19137 : y ≠ y ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1369
       have i₂ := eq18982
       grind)
    | exact superpose eq18982 eq1369
    | (have r₁ := eq1369
       have r₂ := eq18982
       grind)
    | exact resolve eq1369 eq18982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369 eq18982
  have eq19162 : y ≠ y ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq19137
  have eq19163 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq19162
  have eq19767 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq19163
       have i₂ := eq177 (σ x) (σ y)
       grind)
    | exact superpose eq177 eq19163
    | (have j1 := eq177 (σ y) (σ x)
       grind)
    | (have r₁ := eq19163
       have r₂ := eq177 y x
       grind)
    | (have r₁ := eq19163
       have r₂ := eq177 x y
       grind)
    | exact resolve eq19163 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19775 : (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2244 (σ y) (σ x)
       have i₂ := eq19163
       grind)
    | exact superpose eq19163 eq2244
    | (have j0 := eq2244 (σ y) (σ x)
       grind)
    | (have r₁ := eq2244 (σ y) (σ x)
       have r₂ := eq19163
       grind)
    | exact resolve eq2244 eq19163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19776 : (σ y) ≠ (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq19163
  have eq19777 : (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq19775
  have eq19778 : (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq19777
  have eq19786 : (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq19767
  have eq19787 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq19778
       have r₂ := eq19776
       grind)
    | exact resolve eq19778 eq19776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19776 eq19778
  have eq19790 : y = (M.op x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq19787
       have r₂ := eq19786
       grind)
    | exact resolve eq19787 eq19786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19786 eq19787
  have eq20102 : y ≠ y ∨ (M.op y y) = (M.op x x) ∨ (k x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19790
       grind)
    | exact superpose eq19790 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19790
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19790
       grind)
    | exact resolve eq13 eq19790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19790
  have eq20104 : (M.op y y) = (M.op x x) ∨ (k x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq20102
  have eq20109 : (M.op y y) = (k x x) ∨ (k x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq20104
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq20104
    | exact resolve eq20104 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20104
  have eq20111 : (k y y) = (k x x) ∨ (k x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq20109
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq20109
    | exact resolve eq20109 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20109
  have eq20112 : (k y y) = (k x x) ∨ (k x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq20111
  have eq20113 : (k y y) = (k x x) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq20112
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq20112
    | exact resolve eq20112 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20112
  have eq20772 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq4581
       have i₂ := eq20113
       grind)
    | exact superpose eq20113 eq4581
    | (have r₁ := eq4581
       have r₂ := eq20113
       grind)
    | exact resolve eq4581 eq20113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20774 : (k x x) ≠ (k x x) ∨ (k x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq5849
       have i₂ := eq20113
       grind)
    | exact superpose eq20113 eq5849
    | (have r₁ := eq5849
       have r₂ := eq20113
       grind)
    | exact resolve eq5849 eq20113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5849
  have eq20778 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq20113
       grind)
    | exact superpose eq20113 eq10
    | exact resolve eq10 eq20113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20781 : (k x y) ≠ (k x x) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq20113
  have eq20785 : (k x x) ≠ (k x x) ∨ (k x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k x y) = (k y y) := by grind
  clear eq20774
  have eq20786 : (k x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k x y) = (k y y) := by grind
  clear eq20785
  have eq20788 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq20772
  have eq20793 : (σ y) = (M.op (σ x) (σ y)) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq20778
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq20778
    | exact resolve eq20778 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20778
  have eq20797 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k x y) = (k y y) := by
    first
    | (have r₁ := eq20786
       have r₂ := eq20781
       grind)
    | exact resolve eq20786 eq20781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20781 eq20786
  have eq20802 : (k x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20793 eq20797
    | exact resolve eq20797 eq20793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20797
  have eq21745 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq20788
       have i₂ := eq177 (σ x) (σ y)
       grind)
    | exact superpose eq177 eq20788
    | (have j1 := eq177 (σ y) (σ x)
       grind)
    | (have r₁ := eq20788
       have r₂ := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq20788 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20788
  have eq21749 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq21745
  have eq21750 : (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k x y) = (k y y) := by grind
  clear eq21749
  have eq22392 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq20793
       grind)
    | exact superpose eq20793 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20793
       grind)
    | exact resolve eq13 eq20793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20793
  have eq22395 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq22392
  have eq22402 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq22395
       have i₂ := eq174 (σ x)
       grind)
    | exact superpose eq174 eq22395
    | exact resolve eq22395 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22395
  have eq22404 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq22402
       have i₂ := eq174 (σ y)
       grind)
    | exact superpose eq174 eq22402
    | exact resolve eq22402 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22402
  have eq22405 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq22404
  have eq22406 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq22405
       have i₂ := eq174 (σ y)
       grind)
    | exact superpose eq174 eq22405
    | exact resolve eq22405 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22405
  have eq22407 : (k x y) = (k y y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq22406
  have eq22733 : (σ (k x y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq22407
       grind)
    | exact superpose eq22407 eq10
    | exact resolve eq10 eq22407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22407
  have eq22740 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq22733
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq22733
    | exact resolve eq22733 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22733
  have eq22741 : (σ y) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq22740
  have eq23165 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2403 (σ y) (σ x)
       have i₂ := eq22741
       grind)
    | exact superpose eq22741 eq2403
    | (have j0 := eq2403 (σ y) (σ x)
       grind)
    | (have r₁ := eq2403 (σ y) (σ x)
       have r₂ := eq22741
       grind)
    | exact resolve eq2403 eq22741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23168 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq23165
  have eq23169 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq23168
  have eq28164 : (σ (k x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq20802
       grind)
    | exact superpose eq20802 eq10
    | exact resolve eq10 eq20802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20802
  have eq28170 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28164
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq28164
    | exact resolve eq28164 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28164
  have eq28171 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28170
  have eq28532 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq28171
       have i₂ := eq177 (σ x) (σ y)
       grind)
    | exact superpose eq177 eq28171
    | (have j1 := eq177 (σ y) (σ x)
       grind)
    | exact resolve eq28171 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28171
  have eq28560 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq28532
  have eq28567 : (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq22741
       have r₂ := eq21750
       grind)
    | exact resolve eq22741 eq21750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21750
  have eq28571 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq28560
       have r₂ := eq22741
       grind)
    | exact resolve eq28560 eq22741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22741 eq28560
  have eq28947 : (σ (k x y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq28567
       grind)
    | exact superpose eq28567 eq10
    | exact resolve eq10 eq28567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28952 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq28947
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq28947
    | exact resolve eq28947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28947
  have eq28953 : (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq28952
  have eq29017 : (τ (σ y)) = (k x (τ (σ y))) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq11746 x (σ y)
       have i₂ := eq28953
       grind)
    | exact superpose eq28953 eq11746
    | exact resolve eq11746 eq28953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11746
  have eq29130 : y = (k x y) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq29017
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq29017
    | exact resolve eq29017 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29017
  have eq29242 : y ≠ y ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2389
       have i₂ := eq29130
       grind)
    | exact superpose eq29130 eq2389
    | (have r₁ := eq2389
       have r₂ := eq29130
       grind)
    | exact resolve eq2389 eq29130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29250 : y ≠ y ∨ (k y y) = (k x x) ∨ y = (k y y) ∨ (M.op x y) = (k y y) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2403 y x
       have i₂ := eq29130
       grind)
    | exact superpose eq29130 eq2403
    | (have j0 := eq2403 y x
       grind)
    | (have r₁ := eq2403 y x
       have r₂ := eq29130
       grind)
    | exact resolve eq2403 eq29130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403
  have eq29253 : (M.op x y) = (k y y) ∨ y = (k y y) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq29250
  have eq29259 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq29242
  have eq30884 : (σ y) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq29259
       have i₂ := eq177 (σ x) (σ y)
       grind)
    | exact superpose eq177 eq29259
    | (have j1 := eq177 (σ y) (σ x)
       grind)
    | exact resolve eq29259 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29259
  have eq30898 : (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y y) := by
    first
    | (have r₁ := eq30884
       have r₂ := eq28953
       grind)
    | exact resolve eq30884 eq28953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30884
  have eq30902 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12024 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12024
    | exact resolve eq12024 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12024
  have eq31555 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12090 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12090
    | exact resolve eq12090 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12090
  have eq33517 : (M.op (σ x) (σ y)) ≠ (σ (k y y)) ∨ y = (k y y) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq29253
       grind)
    | exact superpose eq29253 eq9
    | exact resolve eq9 eq29253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29253
  have eq33533 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ y = (k y y) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq33517
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq33517
    | exact resolve eq33517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33517
  have eq35447 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ y = (k y y) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq33533
       have i₂ := eq23169
       grind)
    | exact superpose eq23169 eq33533
    | (have r₁ := eq33533
       have r₂ := eq23169
       grind)
    | exact resolve eq33533 eq23169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23169 eq33533
  have eq35460 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ y = (k y y) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq35447
  have eq35461 : y = (k y y) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq35460
  have eq41237 : (σ y) = (k (σ y) (σ y)) ∨ (k y y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq35461
       grind)
    | exact superpose eq35461 eq10
    | exact resolve eq10 eq35461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35461
  have eq41239 : (k y y) = (k x x) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq41237
  have eq41560 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq41239
       grind)
    | exact superpose eq41239 eq10
    | exact resolve eq10 eq41239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41239
  have eq41579 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq41560
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq41560
    | exact resolve eq41560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41560
  have eq41580 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq41579
  have eq41874 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq18 y y
       have i₂ := eq41580
       grind)
    | exact superpose eq41580 eq18
    | exact resolve eq18 eq41580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42005 : (σ y) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  have eq42142 : (k y y) = (k x x) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41874
       have i₂ := eq18 x x
       grind)
    | exact superpose eq18 eq41874
    | exact resolve eq41874 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41874
  have eq42150 : (M.op x y) = (k y y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq41580
       have r₂ := eq30898
       grind)
    | exact resolve eq41580 eq30898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30898 eq41580
  have eq42278 : (M.op x y) = (k x x) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq42142 eq42150
    | exact resolve eq42150 eq42142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42150
  have eq42979 : (k x y) = (k x x) ∨ (k y y) ≠ (k x x) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq42278
       grind)
    | exact superpose eq42278 eq177
    | (have j0 := eq177 y x
       grind)
    | exact resolve eq177 eq42278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42278
  have eq42998 : (k x y) = (k x x) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq42979
       have r₂ := eq42142
       grind)
    | exact resolve eq42979 eq42142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42142 eq42979
  have eq43013 : y = (k x x) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq29130 eq42998
    | exact resolve eq42998 eq29130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42998
  have eq43306 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq43013
       grind)
    | exact superpose eq43013 eq10
    | exact resolve eq10 eq43013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43013
  have eq43310 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq43306
       have r₂ := eq42005
       grind)
    | exact resolve eq43306 eq42005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42005 eq43306
  have eq43325 : (k y y) = (τ (k (σ x) (σ y))) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq18 y y
       have i₂ := eq43310
       grind)
    | exact superpose eq43310 eq18
    | exact resolve eq18 eq43310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43462 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  have eq43599 : (k x y) = (k y y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq43325
       have i₂ := eq18 x y
       grind)
    | exact superpose eq18 eq43325
    | exact resolve eq43325 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43325
  have eq43735 : (k x y) ≠ (k x y) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3105
       have i₂ := eq43599
       grind)
    | exact superpose eq43599 eq3105
    | (have r₁ := eq3105
       have r₂ := eq43599
       grind)
    | exact resolve eq3105 eq43599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43749 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq43735
  have eq46887 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq43749
       have i₂ := eq2244 (σ y) (σ x)
       grind)
    | exact superpose eq2244 eq43749
    | (have j1 := eq2244 (σ y) (σ x)
       grind)
    | (have r₁ := eq43749
       have r₂ := eq2244 (σ y) (σ x)
       grind)
    | exact resolve eq43749 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46889 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq43749
       have i₂ := eq1208 (σ x) (σ y)
       grind)
    | exact superpose eq1208 eq43749
    | (have j1 := eq1208 (σ x) (σ y)
       grind)
    | (have r₁ := eq43749
       have r₂ := eq1208 (σ x) (σ y)
       grind)
    | exact resolve eq43749 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43749
  have eq46893 : (M.op x y) = (k x y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq46889
  have eq46894 : (M.op x y) = (k x y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq46887
  have eq46901 : (M.op x y) = (k x y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq46893
       have r₂ := eq43310
       grind)
    | exact resolve eq46893 eq43310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46893
  have eq46902 : (M.op x y) = (k x y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq43310 eq46894
    | exact resolve eq46894 eq43310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46894
  have eq46905 : (M.op x y) = (k x y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq43310 eq46901
    | exact resolve eq46901 eq43310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46901
  have eq46906 : (M.op x y) = (k x y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq43310 eq46902
    | exact resolve eq46902 eq43310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43310 eq46902
  have eq46910 : (M.op x y) = (k x y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq46906
       have r₂ := eq46905
       grind)
    | exact resolve eq46906 eq46905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46906
  have eq46912 : (M.op x y) = (k x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq28571 eq46910
    | exact resolve eq46910 eq28571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28571 eq46910
  have eq46913 : (M.op x y) = (k x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq46912
  have eq50355 : y = (k x y) ∨ (k x y) ≠ (k y y) ∨ (k y y) = (k x x) ∨ y = (k x y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2244 y x
       have i₂ := eq46905
       grind)
    | exact superpose eq46905 eq2244
    | (have j0 := eq2244 y x
       grind)
    | exact resolve eq2244 eq46905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46905
  have eq50356 : y = (k x y) ∨ (k x y) ≠ (k y y) ∨ (k y y) = (k x x) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq50355
  have eq50360 : (k x y) ≠ (k y y) ∨ y = (k x y) ∨ (k y y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq29130 eq50356
    | exact resolve eq50356 eq29130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29130 eq50356
  have eq50672 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq46913
       grind)
    | exact superpose eq46913 eq9
    | exact resolve eq9 eq46913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50710 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq50672
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq50672
    | exact resolve eq50672 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50672
  have eq55431 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50710
       have i₂ := eq17 (σ x) (σ y)
       grind)
    | exact superpose eq17 eq50710
    | (have j1 := eq17 (σ x) (σ y)
       grind)
    | (have r₁ := eq50710
       have r₂ := eq17 (σ x) (σ y)
       grind)
    | exact resolve eq50710 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55432 : (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq55431
  have eq55441 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55432
       have i₂ := eq174 (σ y)
       grind)
    | exact superpose eq174 eq55432
    | exact resolve eq55432 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55432
  have eq55442 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28953 eq55441
    | exact resolve eq55441 eq28953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55441
  have eq55443 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq55442
       have r₂ := eq50710
       grind)
    | exact resolve eq55442 eq50710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50710 eq55442
  have eq58148 : ∀ X0 : G, (k X0 X0) ≠ (k x y) ∨ (k y X0) = X0 ∨ (k X0 X0) ≠ (k y X0) ∨ (k X0 X0) = (M.op y X0) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4556 X0 y
       have i₂ := eq28567
       grind)
    | exact superpose eq28567 eq4556
    | (have j0 := eq4556 X0 y
       grind)
    | (have r₁ := eq4556 y x
       have r₂ := eq28567
       grind)
    | (have r₁ := eq4556 (σ y) (σ x)
       have r₂ := eq28567
       grind)
    | exact resolve eq4556 eq28567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58152 : ∀ X0 : G, (k y X0) = X0 ∨ (k X0 X0) ≠ (k x y) ∨ (k X0 X0) ≠ (k y X0) ∨ (k X0 X0) = (M.op y X0) ∨ (σ y) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4556 X0 y
       have i₂ := eq43599
       grind)
    | exact superpose eq43599 eq4556
    | (have j0 := eq4556 X0 y
       grind)
    | (have r₁ := eq4556 y x
       have r₂ := eq43599
       grind)
    | exact resolve eq4556 eq43599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4556
  have eq58158 : ∀ X0 : G, (k X0 X0) ≠ (k x y) ∨ (k y X0) = X0 ∨ (k X0 X0) ≠ (k y X0) ∨ (k X0 X0) = (M.op y X0) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq58152 eq58148
    | (have j0 := eq58148 X0
       have j1 := eq58152 X0
       grind)
    | exact resolve eq58148 eq58152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58148 eq58152
  have eq58159 : ∀ X0 : G, (k y X0) = X0 ∨ (k X0 X0) ≠ (k x y) ∨ (k X0 X0) ≠ (k y X0) ∨ (k X0 X0) = (M.op y X0) ∨ (σ y) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq58158 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58158
  have eq63410 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30902 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq30902
    | exact resolve eq30902 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63546 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30902 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq30902
    | exact resolve eq30902 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30902
  have eq64111 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31555 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq31555
    | exact resolve eq31555 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31555
  have eq91662 : y = (k x y) ∨ (k x y) ≠ (k x y) ∨ (k x y) ≠ (k x y) ∨ (k x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq58159 y
       have i₂ := eq28567
       grind)
    | exact superpose eq28567 eq58159
    | (have r₁ := eq58159 y
       have r₂ := eq28567
       grind)
    | exact resolve eq58159 eq28567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28567 eq58159
  have eq91853 : y = (k x y) ∨ (k x y) ≠ (k x y) ∨ (k x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq91662
  have eq91854 : y = (k x y) ∨ (k x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq91853
  have eq91952 : (k x y) = (k y y) ∨ y = (k x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq91854
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq91854
    | exact resolve eq91854 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91854
  have eq91959 : (k x y) = (k y y) ∨ y = (k x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq43599 eq91952
    | exact resolve eq91952 eq43599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91952
  have eq91960 : y = (k x y) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq91959
  have eq92562 : (σ y) = (k (σ x) (σ y)) ∨ (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq91960
       grind)
    | exact superpose eq91960 eq10
    | exact resolve eq10 eq91960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92563 : (k x y) = (k y y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq92562
  have eq92614 : (k x y) ≠ (k x y) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3105
       have i₂ := eq92563
       grind)
    | exact superpose eq92563 eq3105
    | (have r₁ := eq3105
       have r₂ := eq92563
       grind)
    | exact resolve eq3105 eq92563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3105
  have eq92638 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq92614
  have eq92666 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq92638
       have i₂ := eq1208 (σ x) (σ y)
       grind)
    | exact superpose eq1208 eq92638
    | (have j1 := eq1208 (σ x) (σ y)
       grind)
    | (have r₁ := eq92638
       have r₂ := eq1208 (σ x) (σ y)
       grind)
    | exact resolve eq92638 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92638
  have eq92669 : (M.op x y) = (k x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq92666
  have eq92685 : (M.op x y) = (k x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq92669
       have r₂ := eq28953
       grind)
    | exact resolve eq92669 eq28953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92669
  have eq92689 : (M.op x y) = (k x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq28953 eq92685
    | exact resolve eq92685 eq28953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92685
  have eq92691 : (M.op x y) = (k x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq46913 eq92689
    | exact resolve eq92689 eq46913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46913 eq92689
  have eq94426 : y = (k x y) ∨ (k x y) ≠ (k y y) ∨ (k y y) = (k x x) ∨ y = (k x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2244 y x
       have i₂ := eq92691
       grind)
    | exact superpose eq92691 eq2244
    | (have j0 := eq2244 y x
       grind)
    | exact resolve eq2244 eq92691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244 eq92691
  have eq94428 : y = (k x y) ∨ (k x y) ≠ (k y y) ∨ (k y y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq94426
  have eq94440 : y = (k x y) ∨ (k y y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq94428
       have r₂ := eq91960
       grind)
    | exact resolve eq94428 eq91960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94428
  have eq94456 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k x y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq91960 eq94440
    | exact resolve eq94440 eq91960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91960 eq94440
  have eq139585 : (k x y) ≠ (k x y) ∨ y = (k x y) ∨ (k x y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq50360
       have i₂ := eq92563
       grind)
    | exact superpose eq92563 eq50360
    | (have r₁ := eq50360
       have r₂ := eq92563
       grind)
    | exact resolve eq50360 eq92563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50360 eq92563
  have eq139591 : (k x y) ≠ (k x y) ∨ y = (k x y) ∨ (k x y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq139585
  have eq139592 : y = (k x y) ∨ (k x y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq139591
  have eq139610 : y = (k x y) ∨ (k x y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq94456 eq139592
    | exact resolve eq139592 eq94456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94456 eq139592
  have eq140292 : (σ y) = (k (σ x) (σ y)) ∨ (k x y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq139610
       grind)
    | exact superpose eq139610 eq10
    | exact resolve eq10 eq139610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139610
  have eq140294 : (k x y) = (k x x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq140292
  have eq141106 : (k (σ x) (σ y)) = (σ (k x x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq140294
       grind)
    | exact superpose eq140294 eq10
    | exact resolve eq10 eq140294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140294
  have eq141166 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq141106
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq141106
    | exact resolve eq141106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141106
  have eq141167 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq141166
  have eq141226 : (σ y) = (k (σ x) (σ x)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq28953
       have i₂ := eq141167
       grind)
    | exact superpose eq141167 eq28953
    | exact resolve eq28953 eq141167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141479 : (σ y) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  have eq141731 : (σ y) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq141226
       have r₂ := eq141479
       grind)
    | exact resolve eq141226 eq141479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141226 eq141479
  have eq143638 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43462
       have i₂ := eq141731
       grind)
    | exact superpose eq141731 eq43462
    | (have r₁ := eq43462
       have r₂ := eq141731
       grind)
    | exact resolve eq43462 eq141731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143769 : (τ (σ y)) = (k x (τ (σ y))) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq63410 x (σ y)
       have i₂ := eq141731
       grind)
    | exact superpose eq141731 eq63410
    | exact resolve eq63410 eq141731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63410 eq141731
  have eq143897 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq143638
  have eq144015 : y = (k x y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq143769
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq143769
    | exact resolve eq143769 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143769
  have eq451536 : y = (M.op x y) ∨ (M.op x y) = (k y y) ∨ (k x y) = (k y y) := by grind
  clear eq1711 eq4571 eq43599
  have eq632531 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ (k x y) = (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq451536
       grind)
    | exact superpose eq451536 eq9
    | exact resolve eq9 eq451536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451536
  have eq896397 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq18 y y
       have i₂ := eq143897
       grind)
    | exact superpose eq143897 eq18
    | exact resolve eq18 eq143897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143897
  have eq896685 : (σ y) = (k (σ y) (σ y)) ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq896397
       have i₂ := eq18 x x
       grind)
    | exact superpose eq18 eq896397
    | exact resolve eq896397 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896397
  have eq896976 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq63546 y (σ y)
       have i₂ := eq896685
       grind)
    | exact superpose eq896685 eq63546
    | exact resolve eq63546 eq896685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63546
  have eq897007 : y = (k y y) ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq896976
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq896976
    | exact resolve eq896976 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896976
  have eq898190 : y ≠ (k x x) ∨ (k y y) = (k x x) := by grind
  have eq1428790 : (τ (σ y)) = (k x (τ (σ y))) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq64111 x (σ y)
       have i₂ := eq28953
       grind)
    | exact superpose eq28953 eq64111
    | exact resolve eq64111 eq28953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28953 eq64111
  have eq1431685 : y = (k x y) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1428790
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq1428790
    | exact resolve eq1428790 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428790
  have eq1431696 : y = (k x y) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq144015 eq1431685
    | exact resolve eq1431685 eq144015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144015 eq1431685
  have eq1454178 : y ≠ y ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2389
       have i₂ := eq1431696
       grind)
    | exact superpose eq1431696 eq2389
    | (have r₁ := eq2389
       have r₂ := eq1431696
       grind)
    | exact resolve eq2389 eq1431696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389 eq1431696
  have eq1454284 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1454178
  have eq1481206 : (σ y) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1454284
       have i₂ := eq17 (σ x) (σ y)
       grind)
    | exact superpose eq17 eq1454284
    | (have j1 := eq17 (σ x) (σ y)
       grind)
    | (have r₁ := eq1454284
       have r₂ := eq17 (σ x) (σ y)
       grind)
    | exact resolve eq1454284 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1481226 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1481206
       have i₂ := eq174 (σ y)
       grind)
    | exact superpose eq174 eq1481206
    | exact resolve eq1481206 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq1481206
  have eq1481233 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43462 eq1481226
    | exact resolve eq1481226 eq43462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481226
  have eq1481234 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1481233
  have eq1481238 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq1481234
       have r₂ := eq55443
       grind)
    | exact resolve eq1481234 eq55443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55443 eq1481234
  have eq1481241 : (M.op x y) = (k y y) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq1481238
       have r₂ := eq1454284
       grind)
    | exact resolve eq1481238 eq1454284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454284 eq1481238
  have eq1505484 : (M.op (σ x) (σ y)) ≠ (σ (k y y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1481241
       grind)
    | exact superpose eq1481241 eq9
    | exact resolve eq9 eq1481241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481241
  have eq1505515 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1505484
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq1505484
    | exact resolve eq1505484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505484
  have eq2294399 : (σ y) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1505515
       have i₂ := eq1208 (σ x) (σ y)
       grind)
    | exact superpose eq1208 eq1505515
    | (have j1 := eq1208 (σ x) (σ y)
       grind)
    | (have r₁ := eq1505515
       have r₂ := eq1208 (σ x) (σ y)
       grind)
    | exact resolve eq1505515 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq2294412 : (σ y) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq141167 eq2294399
    | exact resolve eq2294399 eq141167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294399
  have eq2294413 : (σ y) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq2294412
  have eq2294415 : (k (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq43462 eq141167 eq1505515 eq2294413
  have eq2294465 : (k x y) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq18 x y
       have i₂ := eq2294415
       grind)
    | exact superpose eq2294415 eq18
    | exact resolve eq18 eq2294415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2295056 : (k x y) = (k x x) := by
    first
    | (have i₁ := eq2294465
       have i₂ := eq18 x x
       grind)
    | exact superpose eq18 eq2294465
    | exact resolve eq2294465 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2294465
  have eq2295279 : (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1536
       have r₂ := eq2295056
       grind)
    | exact resolve eq1536 eq2295056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq2295293 : (k y y) = (k x x) ∨ (M.op x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2295279
       have i₂ := eq2295056
       grind)
    | exact superpose eq2295056 eq2295279
    | exact resolve eq2295279 eq2295056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295279
  have eq2295303 : (k y y) = (k x x) ∨ (M.op x y) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq896685 eq2295293
    | exact resolve eq2295293 eq896685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896685 eq2295293
  have eq2295304 : (k y y) = (k x x) ∨ (M.op x y) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2295303
  have eq2295313 : y = (M.op x y) ∨ (k y y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq897007 eq2295304
    | exact resolve eq2295304 eq897007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295304
  have eq2297582 : y ≠ (k y y) ∨ (k y y) = (k x x) ∨ (k x y) = (k y y) ∨ y = (k x y) ∨ (k y y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15211 y x
       have i₂ := eq2295313
       grind)
    | exact superpose eq2295313 eq15211
    | (have j0 := eq15211 y x
       grind)
    | exact resolve eq15211 eq2295313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15211 eq2295313
  have eq2297583 : y ≠ (k y y) ∨ (k y y) = (k x x) ∨ (k x y) = (k y y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2297582
  have eq2297605 : (k y y) = (k x x) ∨ y ≠ (k y y) ∨ (k y y) = (k x x) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2297583
       have i₂ := eq2295056
       grind)
    | exact superpose eq2295056 eq2297583
    | exact resolve eq2297583 eq2295056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297583
  have eq2297606 : (k y y) = (k x x) ∨ y ≠ (k y y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2297605
  have eq2297632 : y = (k x x) ∨ (k y y) = (k x x) ∨ y ≠ (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2297606
       have i₂ := eq2295056
       grind)
    | exact superpose eq2295056 eq2297606
    | exact resolve eq2297606 eq2295056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297606
  have eq2297662 : y = (k x x) ∨ (k y y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2297632
       have r₂ := eq897007
       grind)
    | exact resolve eq2297632 eq897007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297632
  have eq2297681 : (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) := by
    first
    | (have r₁ := eq2297662
       have r₂ := eq898190
       grind)
    | exact resolve eq2297662 eq898190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297662
  have eq2298883 : (σ y) ≠ (σ y) ∨ (M.op x y) ≠ (k y y) ∨ (k y y) = (k x x) ∨ y = (k x y) ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq15194
       have i₂ := eq2297681
       grind)
    | exact superpose eq2297681 eq15194
    | (have r₁ := eq15194
       have r₂ := eq2297681
       grind)
    | exact resolve eq15194 eq2297681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15194
  have eq2298908 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k y y) ∨ (k x y) = (k y y) ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq632531
       have i₂ := eq2297681
       grind)
    | exact superpose eq2297681 eq632531
    | (have r₁ := eq632531
       have r₂ := eq2297681
       grind)
    | exact resolve eq632531 eq2297681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632531 eq2297681
  have eq2298917 : (M.op x y) = (k y y) ∨ (k x y) = (k y y) ∨ (k y y) = (k x x) := by grind
  clear eq2298908
  have eq2298935 : (σ y) ≠ (σ y) ∨ (M.op x y) ≠ (k y y) ∨ (k y y) = (k x x) ∨ y = (k x y) := by grind
  clear eq2298883
  have eq2298936 : (M.op x y) ≠ (k y y) ∨ (k y y) = (k x x) ∨ y = (k x y) := by grind
  clear eq2298935
  have eq2298944 : (k y y) = (k x x) ∨ (M.op x y) = (k y y) ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq2298917
       have i₂ := eq2295056
       grind)
    | exact superpose eq2295056 eq2298917
    | exact resolve eq2298917 eq2295056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298917
  have eq2298945 : (k y y) = (k x x) ∨ (M.op x y) = (k y y) := by grind
  clear eq2298944
  have eq2298958 : y = (k x x) ∨ (M.op x y) ≠ (k y y) ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq2298936
       have i₂ := eq2295056
       grind)
    | exact superpose eq2295056 eq2298936
    | exact resolve eq2298936 eq2295056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295056 eq2298936
  have eq2298972 : (k y y) = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq897007 eq2298945
    | exact resolve eq2298945 eq897007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298945
  have eq2298982 : y = (k x x) ∨ y ≠ (M.op x y) ∨ (k y y) = (k x x) := by
    first
    | exact superpose eq897007 eq2298958
    | exact resolve eq2298958 eq897007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897007 eq2298958
  have eq2299000 : y = (k x x) ∨ (k y y) = (k x x) := by
    first
    | (have r₁ := eq2298982
       have r₂ := eq2298972
       grind)
    | exact resolve eq2298982 eq2298972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298972 eq2298982
  have eq2299007 : (k y y) = (k x x) := by
    first
    | (have r₁ := eq2299000
       have r₂ := eq898190
       grind)
    | exact resolve eq2299000 eq898190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898190 eq2299000
  have eq2299010 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq4581
       have r₂ := eq2299007
       grind)
    | exact resolve eq4581 eq2299007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4581
  have eq2299020 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2299010
       have i₂ := eq2294415
       grind)
    | exact superpose eq2294415 eq2299010
    | exact resolve eq2299010 eq2294415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2299010
  have eq2301361 : (k (σ y) (σ y)) = (σ (k x x)) := by
    first
    | (have i₁ := eq23 y y
       have i₂ := eq2299007
       grind)
    | exact superpose eq2299007 eq23
    | exact resolve eq23 eq2299007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2299007
  have eq2301393 : (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2301361
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2301361
    | exact resolve eq2301361 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2301361
  have eq2303782 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2299020
       have i₂ := eq177 (σ x) (σ y)
       grind)
    | exact superpose eq177 eq2299020
    | (have j1 := eq177 (σ y) (σ x)
       grind)
    | exact resolve eq2299020 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2299020
  have eq2303791 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2303782
       have i₂ := eq2294415
       grind)
    | exact superpose eq2294415 eq2303782
    | (have r₁ := eq2303782
       have r₂ := eq2294415
       grind)
    | exact resolve eq2303782 eq2294415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294415 eq2303782
  have eq2303792 : (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq2303791
  have eq2303813 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2303792
       have i₂ := eq2301393
       grind)
    | exact superpose eq2301393 eq2303792
    | (have r₁ := eq2303792
       have r₂ := eq2301393
       grind)
    | exact resolve eq2303792 eq2301393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2301393 eq2303792
  have eq2303814 : False := by grind
  exact eq2303814

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = m(Y,Y) then Y else if m(Y,X) = Y then m(Y,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyy_pyx_pyy_pyx_y_pyx_y_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq16
    | exact resolve eq16 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq17
    | exact resolve eq17 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq20
    | exact resolve eq20 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq61 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq29
    | exact resolve eq29 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq109 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq61
    | exact resolve eq61 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq173 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) ≠ (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 X1
       have i₂ := eq173 X1
       grind)
    | exact superpose eq173 eq175
    | (have j0 := eq175 X0 X1
       grind)
    | (have r₁ := eq175 X0 X0
       have r₂ := eq173 X0
       grind)
    | exact resolve eq175 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq200 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq109 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq109
    | exact resolve eq109 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq384 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq200 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq200
    | exact resolve eq200 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq711 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq384 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq384
    | exact resolve eq384 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq384 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq384
    | exact resolve eq384 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq1202 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq9
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq9 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1204 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1207 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1205 X0 X1
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq1205
    | (have j0 := eq1205 X0 X1
       grind)
    | exact resolve eq1205 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1208 : ∀ X0 X1 : G, (k X1 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1204 X0 X1
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq1204
    | (have j0 := eq1204 X0 X1
       grind)
    | (have r₁ := eq1204 X0 X0
       have r₂ := eq173 X0
       grind)
    | exact resolve eq1204 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1210 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1202
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq1202
    | exact resolve eq1202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1211 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1207 X0 X1
       have i₂ := eq173 X1
       grind)
    | exact superpose eq173 eq1207
    | (have j0 := eq1207 X0 X1
       grind)
    | exact resolve eq1207 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1212 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ (k X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1208 X0 X1
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq1208
    | (have j0 := eq1208 X0 X1
       grind)
    | exact resolve eq1208 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1214 : (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1210
       have i₂ := eq173 x
       grind)
    | exact superpose eq173 eq1210
    | exact resolve eq1210 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1215 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ X0 ∨ (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1211 X0 X1
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq1211
    | (have j0 := eq1211 X0 X1
       grind)
    | exact resolve eq1211 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1216 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ (k X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1212 X0 X1
       have i₂ := eq173 X1
       grind)
    | exact superpose eq173 eq1212
    | (have j0 := eq1212 X0 X1
       grind)
    | exact resolve eq1212 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1218 : (M.op x x) = (k y y) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1214
       have i₂ := eq173 y
       grind)
    | exact superpose eq173 eq1214
    | exact resolve eq1214 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1219 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1216 X0 X1
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq1216
    | (have j0 := eq1216 X0 X1
       grind)
    | exact resolve eq1216 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1221 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k x x) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1218
       have i₂ := eq173 x
       grind)
    | exact superpose eq173 eq1218
    | exact resolve eq1218 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1297 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k x x) = (k y y) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1221
       have i₂ := eq11 (σ y) (σ x)
       grind)
    | exact superpose eq11 eq1221
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq1221
       have r₂ := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq1221 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1298 : (M.op x y) = (k x x) ∨ (k x x) = (k y y) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq1297
  have eq1299 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k x x) = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1298
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq1298
    | exact resolve eq1298 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1300 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k x x) = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1299
       have i₂ := eq173 (σ y)
       grind)
    | exact superpose eq173 eq1299
    | exact resolve eq1299 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq1301 : (k x x) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1300
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq1300
    | exact resolve eq1300 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq1378 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1301
       grind)
    | exact superpose eq1301 eq10
    | exact resolve eq10 eq1301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq1379 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1378
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1378
    | exact resolve eq1378 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1380 : x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1379
  have eq1465 : x ≠ (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq1472 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq711 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq711
    | exact resolve eq711 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq1551 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq727 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq727
    | exact resolve eq727 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq2239 : x ≠ x ∨ x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1380
       grind)
    | exact superpose eq1380 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1380
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1380
       grind)
    | exact resolve eq12 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380
  have eq2240 : x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2239
  have eq2242 : x = (k x x) ∨ (M.op x x) = (M.op y y) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2240
       have i₂ := eq173 x
       grind)
    | exact superpose eq173 eq2240
    | exact resolve eq2240 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2240
  have eq2244 : (M.op x x) = (k y y) ∨ x = (k x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2242
       have i₂ := eq173 y
       grind)
    | exact superpose eq173 eq2242
    | exact resolve eq2242 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242
  have eq2246 : (k x x) = (k y y) ∨ x = (k x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2244
       have i₂ := eq173 x
       grind)
    | exact superpose eq173 eq2244
    | exact resolve eq2244 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq2248 : (k y x) = (k x x) ∨ (k x x) = (k y y) ∨ x = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2246
       have i₂ := eq173 x
       grind)
    | exact superpose eq173 eq2246
    | exact resolve eq2246 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246
  have eq2250 : (k y x) = (k x x) ∨ (k x x) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2248
       have r₂ := eq1465
       grind)
    | exact resolve eq2248 eq1465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465 eq2248
  have eq2252 : (k (σ y) (σ x)) = (σ (k x x)) ∨ (k x x) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq2250
       grind)
    | exact superpose eq2250 eq10
    | exact resolve eq10 eq2250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2250
  have eq2253 : (k x x) = (k y y) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2252
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2252
    | exact resolve eq2252 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2252
  have eq2326 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq2253
       grind)
    | exact superpose eq2253 eq10
    | exact resolve eq10 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253
  have eq2327 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2326
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2326
    | exact resolve eq2326 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2326
  have eq2328 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2327
  have eq2405 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2328
       grind)
    | exact superpose eq2328 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq2328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328
  have eq2410 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2405
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq2405
    | (have r₁ := eq2405
       have r₂ := eq173 (σ x)
       grind)
    | exact resolve eq2405 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405
  have eq2411 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2410
  have eq2413 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2411
       have i₂ := eq173 (σ y)
       grind)
    | exact superpose eq173 eq2411
    | exact resolve eq2411 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2411
  have eq2415 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2413
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq2413
    | exact resolve eq2413 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413
  have eq2416 : (M.op x y) = (k x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2415
  have eq2492 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq176 y x
       grind)
    | exact superpose eq176 eq9
    | (have j1 := eq176 x y
       grind)
    | exact resolve eq9 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2512 : (k x x) ≠ (k y y) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2492
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq2492
    | exact resolve eq2492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2492
  have eq2740 : (M.op x x) ≠ (k x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2416
       grind)
    | exact superpose eq2416 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq2416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416
  have eq2742 : (k x x) ≠ (k x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2740
       have i₂ := eq173 x
       grind)
    | exact superpose eq173 eq2740
    | (have r₁ := eq2740
       have r₂ := eq173 x
       grind)
    | exact resolve eq2740 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2740
  have eq2743 : (M.op x x) = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2742
  have eq2746 : (M.op x x) = (k y y) ∨ x = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2743
       have i₂ := eq173 y
       grind)
    | exact superpose eq173 eq2743
    | exact resolve eq2743 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2743
  have eq2748 : x = (k y x) ∨ (k x x) = (k y y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2746
       have i₂ := eq173 x
       grind)
    | exact superpose eq173 eq2746
    | exact resolve eq2746 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2746
  have eq2859 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1472 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1472
    | exact resolve eq1472 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq2900 : (σ x) = (k (σ y) (σ x)) ∨ (k x x) = (k y y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq2748
       grind)
    | exact superpose eq2748 eq10
    | exact resolve eq10 eq2748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2748
  have eq2901 : (k x x) = (k y y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2900
  have eq2905 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1551 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1551
    | exact resolve eq1551 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq2978 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq2901
       grind)
    | exact superpose eq2901 eq10
    | exact resolve eq10 eq2901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2901
  have eq2982 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2978
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2978
    | exact resolve eq2978 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2978
  have eq2983 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq2982
  have eq3141 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2983
       grind)
    | exact superpose eq2983 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2983
       grind)
    | exact resolve eq12 eq2983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3142 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2983
       grind)
    | exact superpose eq2983 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq2983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2983
  have eq3143 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq3142
  have eq3144 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq3141
  have eq3149 : (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3143
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq3143
    | exact resolve eq3143 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3143
  have eq3150 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3144
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq3144
    | exact resolve eq3144 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3144
  have eq3152 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3149
       have i₂ := eq173 (σ y)
       grind)
    | exact superpose eq173 eq3149
    | exact resolve eq3149 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3149
  have eq3153 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3150
       have i₂ := eq173 (σ y)
       grind)
    | exact superpose eq173 eq3150
    | exact resolve eq3150 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3150
  have eq3155 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3152
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq3152
    | exact resolve eq3152 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3152
  have eq3156 : (σ x) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by grind
  clear eq3155
  have eq3157 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3153
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq3153
    | exact resolve eq3153 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3153
  have eq3158 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by grind
  clear eq3157
  have eq3161 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3158
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq3158
    | exact resolve eq3158 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3158
  have eq3162 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq3161
  have eq3238 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ X0 ∨ (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq1215 X0 X1
       grind)
    | exact superpose eq1215 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq1215 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq1215 X0 X1
       grind)
    | exact resolve eq12 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3243 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ X0 ∨ (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3238 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3238
  have eq3244 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ X0 ∨ (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3243 X0 X1
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq3243
    | (have j0 := eq3243 X0 X1
       grind)
    | exact resolve eq3243 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3243
  have eq3245 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ X0 ∨ (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3244 X0 X1
       have i₂ := eq173 X1
       grind)
    | exact superpose eq173 eq3244
    | (have j0 := eq3244 X0 X1
       grind)
    | exact resolve eq3244 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3244
  have eq3246 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ X0 ∨ (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3245 X0 X1
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq3245
    | (have j0 := eq3245 X0 X1
       grind)
    | exact resolve eq3245 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3245
  have eq3247 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq3246 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3246
  have eq3248 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 X0) = (k X1 X1) ∨ (k X1 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3247 X0 X1
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq3247
    | (have j0 := eq3247 X0 X1
       grind)
    | exact resolve eq3247 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3247
  have eq3323 : (k y x) = (τ (k (σ x) (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq17 y x
       have i₂ := eq3162
       grind)
    | exact superpose eq3162 eq17
    | exact resolve eq17 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3389 : (k y x) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3323
       have i₂ := eq17 x x
       grind)
    | exact superpose eq17 eq3323
    | exact resolve eq3323 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3323
  have eq5867 : (k y x) ≠ (k x x) ∨ (M.op x y) = (k x x) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1219 x y
       grind)
    | exact superpose eq1219 eq9
    | (have j1 := eq1219 x y
       grind)
    | exact resolve eq9 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5872 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1219 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5883 : (k x x) ≠ (k x x) ∨ (M.op x y) = (k x x) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5867
       have i₂ := eq3389
       grind)
    | exact superpose eq3389 eq5867
    | (have r₁ := eq5867
       have r₂ := eq3389
       grind)
    | exact resolve eq5867 eq3389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5867
  have eq5888 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq5883
  have eq6062 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq5888
       have i₂ := eq1219 (σ x) (σ y)
       grind)
    | exact superpose eq1219 eq5888
    | (have j1 := eq1219 (σ x) (σ y)
       grind)
    | (have r₁ := eq5888
       have r₂ := eq1219 (σ x) (σ y)
       grind)
    | exact resolve eq5888 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219 eq5888
  have eq6067 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq6062
  have eq6068 : (M.op x y) = (k x x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq6067
  have eq6072 : (k x x) = (k y y) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq6068
       have r₂ := eq3162
       grind)
    | exact resolve eq6068 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162 eq6068
  have eq6252 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq6072
       grind)
    | exact superpose eq6072 eq10
    | exact resolve eq10 eq6072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6072
  have eq6258 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6252
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq6252
    | exact resolve eq6252 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6252
  have eq6259 : (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq6258
  have eq6447 : (M.op x x) ≠ (k x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq6259
       grind)
    | exact superpose eq6259 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq6259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6259
  have eq6449 : (k x x) ≠ (k x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6447
       have i₂ := eq173 x
       grind)
    | exact superpose eq173 eq6447
    | (have r₁ := eq6447
       have r₂ := eq173 x
       grind)
    | exact resolve eq6447 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6447
  have eq6450 : (M.op x x) = (M.op y y) ∨ x = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq6449
  have eq6455 : (M.op x x) = (k y y) ∨ x = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6450
       have i₂ := eq173 y
       grind)
    | exact superpose eq173 eq6450
    | exact resolve eq6450 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6450
  have eq6457 : (k x x) = (k y y) ∨ x = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6455
       have i₂ := eq173 x
       grind)
    | exact superpose eq173 eq6455
    | exact resolve eq6455 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6455
  have eq6459 : x = (k x x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3389 eq6457
    | exact resolve eq6457 eq3389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3389 eq6457
  have eq6642 : (σ x) = (k (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq6459
       grind)
    | exact superpose eq6459 eq10
    | exact resolve eq10 eq6459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6459
  have eq6643 : (k x x) = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq6642
  have eq6834 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq6643
       grind)
    | exact superpose eq6643 eq10
    | exact resolve eq10 eq6643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6643
  have eq6840 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6834
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq6834
    | exact resolve eq6834 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6834
  have eq6841 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq6840
  have eq7040 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq6841
       grind)
    | exact superpose eq6841 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq6841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6841
  have eq7041 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq7040
  have eq7049 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq7041
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq7041
    | (have r₁ := eq7041
       have r₂ := eq173 (σ x)
       grind)
    | exact resolve eq7041 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7041
  have eq7050 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq7049
  have eq7054 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq7050
       have i₂ := eq173 (σ y)
       grind)
    | exact superpose eq173 eq7050
    | exact resolve eq7050 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7050
  have eq7056 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq7054
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq7054
    | exact resolve eq7054 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq7054
  have eq7057 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq7056
  have eq7244 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq17 y y
       have i₂ := eq7057
       grind)
    | exact superpose eq7057 eq17
    | exact resolve eq17 eq7057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7344 : (k x x) = (k y y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq7244
       have i₂ := eq17 x x
       grind)
    | exact superpose eq17 eq7244
    | exact resolve eq7244 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7244
  have eq7583 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2512
       have i₂ := eq7344
       grind)
    | exact superpose eq7344 eq2512
    | (have r₁ := eq2512
       have r₂ := eq7344
       grind)
    | exact resolve eq2512 eq7344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7344
  have eq7589 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq7583
  have eq7788 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq7589
       have i₂ := eq176 (σ y) (σ x)
       grind)
    | exact superpose eq176 eq7589
    | (have j1 := eq176 (σ x) (σ y)
       grind)
    | (have r₁ := eq7589
       have r₂ := eq176 (σ y) (σ x)
       grind)
    | exact resolve eq7589 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7589
  have eq7791 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq7788
  have eq7796 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq7791
       have r₂ := eq7057
       grind)
    | exact resolve eq7791 eq7057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7057 eq7791
  have eq7799 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3156
       have i₂ := eq7796
       grind)
    | exact superpose eq7796 eq3156
    | (have r₁ := eq3156
       have r₂ := eq7796
       grind)
    | exact resolve eq3156 eq7796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq7850 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2859 x (σ x)
       have i₂ := eq7796
       grind)
    | exact superpose eq7796 eq2859
    | exact resolve eq2859 eq7796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7855 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq7799
  have eq7856 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq7855
  have eq7857 : x = (k x x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq7850
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq7850
    | exact resolve eq7850 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7850
  have eq7946 : (k y y) = (τ (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq17 y y
       have i₂ := eq7856
       grind)
    | exact superpose eq7856 eq17
    | exact resolve eq17 eq7856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8049 : x = (k y y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq7946
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq7946
    | exact resolve eq7946 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7946
  have eq8110 : x ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2512
       have i₂ := eq8049
       grind)
    | exact superpose eq8049 eq2512
    | exact resolve eq2512 eq8049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8049
  have eq8129 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq8110
       have r₂ := eq7857
       grind)
    | exact resolve eq8110 eq7857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7857 eq8110
  have eq8545 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq8129
       have i₂ := eq176 (σ y) (σ x)
       grind)
    | exact superpose eq176 eq8129
    | (have j1 := eq176 (σ x) (σ y)
       grind)
    | (have r₁ := eq8129
       have r₂ := eq176 (σ y) (σ x)
       grind)
    | exact resolve eq8129 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8129
  have eq8548 : (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq8545
  have eq8553 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) ≠ (k (σ y) (σ y)) := by
    first
    | exact superpose eq7796 eq8548
    | exact resolve eq8548 eq7796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7796 eq8548
  have eq8555 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq8553
       have r₂ := eq7856
       grind)
    | exact resolve eq8553 eq7856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7856 eq8553
  have eq8585 : (τ (σ x)) = (k y (τ (σ x))) := by
    first
    | (have i₁ := eq2905 y (σ x)
       have i₂ := eq8555
       grind)
    | exact superpose eq8555 eq2905
    | exact resolve eq2905 eq8555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2905
  have eq8637 : x = (k y x) := by
    first
    | (have i₁ := eq8585
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq8585
    | exact resolve eq8585 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8585
  have eq10313 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (k X0 X0) = (k X1 X1) ∨ (k X1 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq3248 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3248
  have eq10315 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (k X0 X0) = (k X1 X1) ∨ (k X1 X0) = (k X0 X0) ∨ (k X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq10313 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10313
  have eq16797 : (M.op (σ x) (σ y)) ≠ (σ (k x x)) ∨ (k x x) = (k y y) ∨ (k y x) = (k x x) ∨ x ≠ (k y x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq10315 x y
       grind)
    | exact superpose eq10315 eq9
    | (have j1 := eq10315 x y
       grind)
    | exact resolve eq9 eq10315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17036 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ (k y x) = (k x x) ∨ x ≠ (k y x) := by
    first
    | (have i₁ := eq16797
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq16797
    | exact resolve eq16797 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16797
  have eq17078 : x = (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ x ≠ (k y x) := by
    first
    | (have i₁ := eq17036
       have i₂ := eq8637
       grind)
    | exact superpose eq8637 eq17036
    | (have r₁ := eq17036
       have r₂ := eq8637
       grind)
    | exact resolve eq17036 eq8637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17036
  have eq17090 : x ≠ x ∨ x = (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq17078
       have i₂ := eq8637
       grind)
    | exact superpose eq8637 eq17078
    | (have r₁ := eq17078
       have r₂ := eq8637
       grind)
    | exact resolve eq17078 eq8637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17078
  have eq17091 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ x = (k x x) ∨ (k x x) = (k y y) := by grind
  clear eq17090
  have eq17462 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ x = (k x x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq17091
       have i₂ := eq10315 (σ x) (σ y)
       grind)
    | exact superpose eq10315 eq17091
    | (have j1 := eq10315 (σ x) (σ y)
       grind)
    | (have r₁ := eq17091
       have r₂ := eq10315 (σ x) (σ y)
       grind)
    | (have r₁ := eq17091
       have r₂ := eq10315 x x
       grind)
    | exact resolve eq17091 eq10315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10315
  have eq17464 : (σ x) ≠ (k (σ x) (σ x)) ∨ x = (k x x) ∨ (k x x) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq17091
       have i₂ := eq1215 (σ x) (σ y)
       grind)
    | exact superpose eq1215 eq17091
    | (have j1 := eq1215 (σ x) (σ y)
       grind)
    | (have r₁ := eq17091
       have r₂ := eq1215 (σ x) (σ y)
       grind)
    | (have r₁ := eq17091
       have r₂ := eq1215 x x
       grind)
    | exact resolve eq17091 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17465 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ x = (k x x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq17091
       have i₂ := eq176 (σ y) (σ x)
       grind)
    | exact superpose eq176 eq17091
    | (have j1 := eq176 (σ x) (σ y)
       grind)
    | (have r₁ := eq17091
       have r₂ := eq176 x y
       grind)
    | (have r₁ := eq17091
       have r₂ := eq176 y x
       grind)
    | exact resolve eq17091 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17467 : x = (k x x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by grind
  clear eq17462
  have eq17471 : (σ x) ≠ (k (σ x) (σ x)) ∨ x = (k x x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq17465
       have i₂ := eq8555
       grind)
    | exact superpose eq8555 eq17465
    | exact resolve eq17465 eq8555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17465
  have eq17472 : (σ x) ≠ (σ x) ∨ (σ x) ≠ (k (σ x) (σ x)) ∨ x = (k x x) ∨ (k x x) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq17464
       have i₂ := eq8555
       grind)
    | exact superpose eq8555 eq17464
    | (have r₁ := eq17464
       have r₂ := eq8555
       grind)
    | exact resolve eq17464 eq8555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17464
  have eq17473 : (σ x) ≠ (k (σ x) (σ x)) ∨ x = (k x x) ∨ (k x x) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq17472
  have eq17476 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq17467
       have i₂ := eq8555
       grind)
    | exact superpose eq8555 eq17467
    | (have r₁ := eq17467
       have r₂ := eq8555
       grind)
    | exact resolve eq17467 eq8555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17467
  have eq17479 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq17476
       have i₂ := eq8555
       grind)
    | exact superpose eq8555 eq17476
    | (have r₁ := eq17476
       have r₂ := eq8555
       grind)
    | exact resolve eq17476 eq8555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17476
  have eq17480 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq17479
  have eq17482 : x = (k x x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq17091 eq17473 eq17480
  have eq18041 : ∀ X0 : G, x ≠ x ∨ x = (M.op x X0) ∨ x ≠ (k X0 x) ∨ x = (k X0 X0) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5872 x x
       have i₂ := eq17482
       grind)
    | exact superpose eq17482 eq5872
    | (have j0 := eq5872 x y
       grind)
    | (have r₁ := eq5872 x x
       have r₂ := eq17482
       grind)
    | exact resolve eq5872 eq17482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18043 : (k x x) = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq17482
       grind)
    | exact superpose eq17482 eq10
    | exact resolve eq10 eq17482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18044 : ∀ X0 : G, x = (M.op x X0) ∨ x ≠ (k X0 x) ∨ x = (k X0 X0) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18041 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18041
  have eq19922 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq18043
       grind)
    | exact superpose eq18043 eq10
    | exact resolve eq10 eq18043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18043
  have eq19928 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq19922
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq19922
    | exact resolve eq19922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19922
  have eq19929 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq19928
  have eq20455 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ x ≠ (k y x) ∨ x = (k y y) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq18044 y
       grind)
    | exact superpose eq18044 eq9
    | (have j1 := eq18044 y
       grind)
    | exact resolve eq9 eq18044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18044
  have eq20475 : x ≠ x ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq20455
       have i₂ := eq8637
       grind)
    | exact superpose eq8637 eq20455
    | (have r₁ := eq20455
       have r₂ := eq8637
       grind)
    | exact resolve eq20455 eq8637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20455
  have eq20476 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq20475
  have eq21163 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq17 y y
       have i₂ := eq19929
       grind)
    | exact superpose eq19929 eq17
    | exact resolve eq17 eq19929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21295 : (k x x) = (k y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq21163
       have i₂ := eq17 x x
       grind)
    | exact superpose eq17 eq21163
    | exact resolve eq21163 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq21163
  have eq22134 : (σ x) ≠ (σ x) ∨ x = (k y y) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq20476
       have i₂ := eq1215 (σ x) (σ y)
       grind)
    | exact superpose eq1215 eq20476
    | (have j1 := eq1215 (σ x) (σ y)
       grind)
    | (have r₁ := eq20476
       have r₂ := eq1215 (σ x) (σ y)
       grind)
    | exact resolve eq20476 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215 eq20476
  have eq22137 : (σ x) ≠ (σ x) ∨ x = (k y y) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by grind
  clear eq22134
  have eq22138 : x = (k y y) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by grind
  clear eq22137
  have eq22148 : (σ x) ≠ (σ x) ∨ x = (k y y) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq22138
       have i₂ := eq8555
       grind)
    | exact superpose eq8555 eq22138
    | (have r₁ := eq22138
       have r₂ := eq8555
       grind)
    | exact resolve eq22138 eq8555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22138
  have eq22149 : x = (k y y) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq22148
  have eq22154 : x = (k y y) ∨ (k x x) = (k y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq21295 eq22149
    | exact resolve eq22149 eq21295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22149
  have eq22157 : (σ x) = (M.op (σ x) (σ y)) ∨ (k x x) = (k y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq21295 eq22154
    | exact resolve eq22154 eq21295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22154
  have eq25467 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2512
       have i₂ := eq21295
       grind)
    | exact superpose eq21295 eq2512
    | (have r₁ := eq2512
       have r₂ := eq21295
       grind)
    | exact resolve eq2512 eq21295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21295
  have eq25476 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq25467
  have eq25481 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq25476
       have i₂ := eq8555
       grind)
    | exact superpose eq8555 eq25476
    | exact resolve eq25476 eq8555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25476
  have eq33182 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq25481
       have i₂ := eq176 (σ y) (σ x)
       grind)
    | exact superpose eq176 eq25481
    | (have j1 := eq176 (σ x) (σ y)
       grind)
    | exact resolve eq25481 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25481
  have eq33191 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq33182
       have i₂ := eq8555
       grind)
    | exact superpose eq8555 eq33182
    | (have r₁ := eq33182
       have r₂ := eq8555
       grind)
    | exact resolve eq33182 eq8555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33182
  have eq33192 : (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq33191
  have eq33197 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq33192
       have r₂ := eq19929
       grind)
    | exact resolve eq33192 eq19929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19929 eq33192
  have eq33210 : x = (k x x) ∨ (k x x) = (k y y) := by grind
  clear eq17471 eq17482
  have eq33257 : ∀ X0 : G, x ≠ x ∨ x = (M.op x X0) ∨ x ≠ (k X0 x) ∨ x = (k X0 X0) ∨ (k x x) = (k y y) := by
    intro X0
    first
    | (have i₁ := eq5872 x x
       have i₂ := eq33210
       grind)
    | exact superpose eq33210 eq5872
    | (have j0 := eq5872 x y
       grind)
    | (have r₁ := eq5872 x x
       have r₂ := eq33210
       grind)
    | exact resolve eq5872 eq33210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5872 eq33210
  have eq33260 : ∀ X0 : G, x = (M.op x X0) ∨ x ≠ (k X0 x) ∨ x = (k X0 X0) ∨ (k x x) = (k y y) := by
    intro X0
    first
    | (have j0 := eq33257 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33257
  have eq34132 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ x ≠ (k y x) ∨ x = (k y y) ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq33260 y
       grind)
    | exact superpose eq33260 eq9
    | (have j1 := eq33260 y
       grind)
    | exact resolve eq9 eq33260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33260
  have eq34154 : x ≠ x ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq34132
       have i₂ := eq8637
       grind)
    | exact superpose eq8637 eq34132
    | (have r₁ := eq34132
       have r₂ := eq8637
       grind)
    | exact resolve eq34132 eq8637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8637 eq34132
  have eq34155 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ (k x x) = (k y y) := by grind
  clear eq34154
  have eq34678 : (τ (σ x)) = (k (τ (σ x)) x) := by
    first
    | (have i₁ := eq2859 x (σ x)
       have i₂ := eq33197
       grind)
    | exact superpose eq33197 eq2859
    | exact resolve eq2859 eq33197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859
  have eq34685 : x = (k x x) := by
    first
    | (have i₁ := eq34678
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq34678
    | exact resolve eq34678 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34678
  have eq36363 : (σ x) ≠ (σ x) ∨ x = (k y y) ∨ (k x x) = (k y y) ∨ (k x x) = (k y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq34155
       have i₂ := eq22157
       grind)
    | exact superpose eq22157 eq34155
    | (have r₁ := eq34155
       have r₂ := eq22157
       grind)
    | exact resolve eq34155 eq22157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22157
  have eq36370 : (σ x) ≠ (k (σ y) (σ x)) ∨ x = (k y y) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq34155
       have i₂ := eq176 (σ y) (σ x)
       grind)
    | exact superpose eq176 eq34155
    | (have j1 := eq176 (σ x) (σ y)
       grind)
    | (have r₁ := eq34155
       have r₂ := eq176 x y
       grind)
    | (have r₁ := eq34155
       have r₂ := eq176 y x
       grind)
    | exact resolve eq34155 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34155
  have eq36375 : (σ x) ≠ (σ x) ∨ x = (k y y) ∨ (k x x) = (k y y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq36363
  have eq36376 : x = (k y y) ∨ (k x x) = (k y y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq36375
  have eq36381 : (σ x) ≠ (σ x) ∨ x = (k y y) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36370
       have i₂ := eq8555
       grind)
    | exact superpose eq8555 eq36370
    | (have r₁ := eq36370
       have r₂ := eq8555
       grind)
    | exact resolve eq36370 eq8555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36370
  have eq36382 : x = (k y y) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq36381
  have eq36393 : x = (k y y) ∨ x = (k y y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36376
       have i₂ := eq34685
       grind)
    | exact superpose eq34685 eq36376
    | exact resolve eq36376 eq34685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36376
  have eq36394 : x = (k y y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq36393
  have eq36399 : x = (k y y) ∨ x = (k y y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36382
       have i₂ := eq34685
       grind)
    | exact superpose eq34685 eq36382
    | exact resolve eq36382 eq34685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36382
  have eq36400 : x = (k y y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq36399
  have eq36408 : (σ x) ≠ (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq36400
       have i₂ := eq33197
       grind)
    | exact superpose eq33197 eq36400
    | exact resolve eq36400 eq33197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36400
  have eq36416 : x = (k y y) := by
    first
    | (have r₁ := eq36408
       have r₂ := eq36394
       grind)
    | exact resolve eq36408 eq36394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36394 eq36408
  have eq36436 : x ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2512
       have i₂ := eq36416
       grind)
    | exact superpose eq36416 eq2512
    | exact resolve eq2512 eq36416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512
  have eq36452 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq36416
       grind)
    | exact superpose eq36416 eq10
    | exact resolve eq10 eq36416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36416
  have eq36458 : x ≠ x ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq36436
       have i₂ := eq34685
       grind)
    | exact superpose eq34685 eq36436
    | (have r₁ := eq36436
       have r₂ := eq34685
       grind)
    | exact resolve eq36436 eq34685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34685 eq36436
  have eq36459 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by grind
  clear eq36458
  have eq36464 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36459
       have i₂ := eq8555
       grind)
    | exact superpose eq8555 eq36459
    | exact resolve eq36459 eq8555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36459
  have eq42337 : (σ x) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36464
       have i₂ := eq176 (σ y) (σ x)
       grind)
    | exact superpose eq176 eq36464
    | (have j1 := eq176 (σ x) (σ y)
       grind)
    | exact resolve eq36464 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq36464
  have eq42343 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq42337
       have i₂ := eq8555
       grind)
    | exact superpose eq8555 eq42337
    | (have r₁ := eq42337
       have r₂ := eq8555
       grind)
    | exact resolve eq42337 eq8555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8555 eq42337
  have eq42344 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq42343
  have eq42350 : (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq42344
       have i₂ := eq36452
       grind)
    | exact superpose eq36452 eq42344
    | exact resolve eq42344 eq36452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36452 eq42344
  have eq42357 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq42350
       have i₂ := eq33197
       grind)
    | exact superpose eq33197 eq42350
    | (have r₁ := eq42350
       have r₂ := eq33197
       grind)
    | exact resolve eq42350 eq33197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33197 eq42350
  have eq42358 : False := by grind
  exact eq42358

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then m(X,X) else if m(X,X) = m(Y,X) then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyy_pyx_x_pxx_pyx_pyx_pxx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = a ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19
    | exact resolve eq19 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq40 (σ X0)
       grind)
    | exact superpose eq40 eq42
    | exact resolve eq42 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22
    | exact resolve eq22 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq66 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0 X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq46
    | exact resolve eq46 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq40 (τ X0)
       grind)
    | exact superpose eq40 eq66
    | exact resolve eq66 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq66
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (k (σ X1) (σ X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq89 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq82
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq82
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq82 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq90 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq89
  have eq106 : (M.op (τ (σ y)) (τ (σ y))) = (τ (M.op (σ x) (σ x))) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq69 (σ y)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq69
    | exact resolve eq69 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq120 : (M.op (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq69 (σ x)
       grind)
    | exact superpose eq69 eq106
    | exact resolve eq106 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq123 : (M.op x x) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq120
    | exact resolve eq120 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq123
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq123
    | exact resolve eq123 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq125 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq124
  have eq128 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 (σ y) X0
       have i₂ := eq125
       grind)
    | exact superpose eq125 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq125
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq125
       grind)
    | exact resolve eq13 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq260 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq128 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq261 : y = (M.op x y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq260
  have eq269 : y ≠ y ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k y x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq261
       grind)
    | exact superpose eq261 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq261
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq261
       grind)
    | exact resolve eq12 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq270 : y ≠ y ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k y x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq269
  have eq271 : (M.op y y) = (k y x) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq270
  have eq292 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq271
       grind)
    | exact superpose eq271 eq15
    | exact resolve eq15 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq295 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq292
       have i₂ := eq43 y
       grind)
    | exact superpose eq43 eq292
    | exact resolve eq292 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq297 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq295
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq295 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq300 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq14 (σ y) (σ x)
       have i₂ := eq297
       grind)
    | exact superpose eq297 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : (τ (M.op (σ y) (σ y))) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq46 (σ x) (σ y)
       have i₂ := eq297
       grind)
    | exact superpose eq297 eq46
    | exact resolve eq46 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq304 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq300
  have eq308 : (τ (M.op (σ y) (σ y))) = (k (τ (σ y)) x) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq301
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq301
    | exact resolve eq301 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq309 : (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq304
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq304
       have r₂ := eq13 y x
       grind)
    | exact resolve eq304 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq311 : (τ (M.op (σ y) (σ y))) = (k y x) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq308
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq308
    | exact resolve eq308 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq312 : (M.op (τ (σ y)) (τ (σ y))) = (k y x) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq311
       have i₂ := eq69 (σ y)
       grind)
    | exact superpose eq69 eq311
    | exact resolve eq311 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq313 : (M.op y y) = (k y x) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq312
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq312
    | exact resolve eq312 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq317 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq313
       grind)
    | exact superpose eq313 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq320 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq317
  have eq324 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq320
       grind)
    | exact superpose eq320 eq16
    | exact resolve eq16 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq332 : (σ y) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq324
       have r₂ := eq309
       grind)
    | exact resolve eq324 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq324
  have eq345 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq46 (σ x) (σ y)
       have i₂ := eq332
       grind)
    | exact superpose eq332 eq46
    | exact resolve eq46 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq354 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq345
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq345
    | exact resolve eq345 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq355 : y = (k y x) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq354
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq354
    | exact resolve eq354 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq363 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq355
       grind)
    | exact superpose eq355 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq363
  have eq395 : y ≠ y ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq366
       grind)
    | exact superpose eq366 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq366
       grind)
    | exact resolve eq12 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : y ≠ y ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq395
  have eq397 : (M.op y y) = (k y x) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq396
  have eq409 : y = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq355
       have i₂ := eq397
       grind)
    | exact superpose eq397 eq355
    | exact resolve eq355 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq397
  have eq414 : y = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq409
  have eq425 : y ≠ (M.op x y) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq414
  have eq426 : (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq425
       have r₂ := eq366
       grind)
    | exact resolve eq425 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq425
  have eq434 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq43 y
       have i₂ := eq426
       grind)
    | exact superpose eq426 eq43
    | exact resolve eq43 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq440 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq434
       have i₂ := eq43 x
       grind)
    | exact superpose eq43 eq434
    | exact resolve eq434 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq441 : (M.op x y) = (M.op y y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq440
  have eq450 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = (M.op X0 y) ∨ (M.op X0 X0) = (M.op y y) ∨ y = (k y X0) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq441
       grind)
    | exact superpose eq441 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq441
       grind)
    | exact resolve eq13 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq43 y
       have i₂ := eq441
       grind)
    | exact superpose eq441 eq43
    | exact resolve eq43 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq464 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq451
       grind)
    | exact superpose eq451 eq16
    | exact resolve eq16 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : y = (k y x) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq450 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq778 : (σ y) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq751
       grind)
    | exact superpose eq751 eq15
    | exact resolve eq15 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq820 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14 (σ y) (σ x)
       have i₂ := eq778
       grind)
    | exact superpose eq778 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq823 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq820
  have eq833 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq823
       have r₂ := eq464
       grind)
    | exact resolve eq823 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq850 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq833
       grind)
    | exact superpose eq833 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq833
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq833
       grind)
    | exact resolve eq12 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq851 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq850
  have eq852 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq851
  have eq921 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq778
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq778
    | exact resolve eq778 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq923 : (τ (M.op (σ y) (σ y))) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq46 (σ x) (σ y)
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq46
    | exact resolve eq46 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq852
  have eq926 : y = (M.op x y) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq921
  have eq935 : (τ (M.op (σ y) (σ y))) = (k (τ (σ y)) x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq923
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq923
    | exact resolve eq923 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq936 : (τ (M.op (σ y) (σ y))) = (k y x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq935
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq935
    | exact resolve eq935 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq937 : (M.op (τ (σ y)) (τ (σ y))) = (k y x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq936
       have i₂ := eq69 (σ y)
       grind)
    | exact superpose eq69 eq936
    | exact resolve eq936 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq938 : (M.op y y) = (k y x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq937
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq937
    | exact resolve eq937 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq939 : (M.op y y) = (k y x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq938
       have r₂ := eq12 y x
       grind)
    | exact resolve eq938 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq947 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq939
       grind)
    | exact superpose eq939 eq15
    | exact resolve eq15 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq954 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq947
       have i₂ := eq43 y
       grind)
    | exact superpose eq43 eq947
    | exact resolve eq947 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq985 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq14 (σ y) (σ x)
       have i₂ := eq954
       grind)
    | exact superpose eq954 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq988 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq985
  have eq999 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have r₁ := eq988
       have r₂ := eq464
       grind)
    | exact resolve eq988 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1055 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq451
       have i₂ := eq926
       grind)
    | exact superpose eq926 eq451
    | exact resolve eq451 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq926
  have eq1068 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq1055
  have eq1080 : (M.op (τ (σ y)) (τ (σ y))) = (τ (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq69 (σ y)
       have i₂ := eq1068
       grind)
    | exact superpose eq1068 eq69
    | exact resolve eq69 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1098 : (M.op (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq1080
       have i₂ := eq69 (σ x)
       grind)
    | exact superpose eq69 eq1080
    | exact resolve eq1080 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080
  have eq1102 : (M.op x x) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq1098
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1098
    | exact resolve eq1098 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1103 : (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq1102
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1102
    | exact resolve eq1102 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1104 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq1103
  have eq1109 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq464
       have i₂ := eq1104
       grind)
    | exact superpose eq1104 eq464
    | exact resolve eq464 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq1104
  have eq1140 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have r₁ := eq1109
       have r₂ := eq999
       grind)
    | exact resolve eq1109 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999 eq1109
  have eq1224 : (M.op (τ (σ y)) (τ (σ y))) = (τ (M.op (σ x) (σ x))) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq69 (σ y)
       have i₂ := eq1140
       grind)
    | exact superpose eq1140 eq69
    | exact resolve eq69 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1243 : (M.op (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq1224
       have i₂ := eq69 (σ x)
       grind)
    | exact superpose eq69 eq1224
    | exact resolve eq1224 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1224
  have eq1246 : (M.op x x) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq1243
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1243
    | exact resolve eq1243 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1247 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq1246
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1246
    | exact resolve eq1246 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1248 : (M.op y y) = (M.op x x) := by grind
  clear eq1247
  have eq1321 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq11 y X0
       have i₂ := eq1248
       grind)
    | exact superpose eq1248 eq11
    | (have j0 := eq11 X0 x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq1248
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq1248
       grind)
    | exact resolve eq11 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1324 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43 y
       have i₂ := eq1248
       grind)
    | exact superpose eq1248 eq43
    | exact resolve eq43 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1328 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1324
       have i₂ := eq43 x
       grind)
    | exact superpose eq43 eq1324
    | exact resolve eq1324 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1324
  have eq1352 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq11 (σ y) X0
       have i₂ := eq1328
       grind)
    | exact superpose eq1328 eq11
    | (have j0 := eq11 X0 (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq1328
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq1328
       grind)
    | exact resolve eq11 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq1365 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq1321 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1369 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq1365
       grind)
    | exact superpose eq1365 eq15
    | exact resolve eq15 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq1370 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1369
       grind)
    | exact superpose eq1369 eq16
    | exact resolve eq16 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1461 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j0 := eq1352 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq1463 : False := by grind
  exact eq1463

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = X then Y else if m(Y,X) = Y then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyy_pyx_x_pyx_y_pxy_y_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq16
    | exact resolve eq16 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq17
    | exact resolve eq17 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq18
    | exact resolve eq18 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq47 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq23
    | exact resolve eq23 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq75 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq47
    | exact resolve eq47 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq159 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq75
    | exact resolve eq75 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq173 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) ≠ (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 X1
       have i₂ := eq173 X1
       grind)
    | exact superpose eq173 eq175
    | (have j0 := eq175 X0 X1
       grind)
    | (have r₁ := eq175 X0 X0
       have r₂ := eq173 X0
       grind)
    | exact resolve eq175 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq275 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq159 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq159
    | exact resolve eq159 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq610 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq275 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq275
    | exact resolve eq275 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq1057 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq610 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq610
    | exact resolve eq610 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq2194 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq9
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq9 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2197 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2198 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2201 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2198 X0 X1
       have i₂ := eq173 X1
       grind)
    | exact superpose eq173 eq2198
    | (have j0 := eq2198 X0 X1
       grind)
    | exact resolve eq2198 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2198
  have eq2202 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2197 X0 X1
       have i₂ := eq173 X1
       grind)
    | exact superpose eq173 eq2197
    | (have j0 := eq2197 X0 X1
       grind)
    | exact resolve eq2197 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2197
  have eq2205 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq2194
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq2194
    | exact resolve eq2194 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194
  have eq2206 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) ≠ X0 ∨ (k X0 X0) = (k X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2201 X0 X1
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq2201
    | (have j0 := eq2201 X0 X1
       grind)
    | exact resolve eq2201 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201
  have eq2207 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) ≠ X1 ∨ (k X0 X0) = (k X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2202 X0 X1
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq2202
    | (have j0 := eq2202 X0 X1
       grind)
    | exact resolve eq2202 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202
  have eq2210 : (M.op y y) = (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2205
       have i₂ := eq173 x
       grind)
    | exact superpose eq173 eq2205
    | exact resolve eq2205 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205
  have eq2211 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (k x x) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2210
       have i₂ := eq173 y
       grind)
    | exact superpose eq173 eq2210
    | exact resolve eq2210 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2210
  have eq2212 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (k x x) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2211
       have i₂ := eq11 (σ y) (σ x)
       grind)
    | exact superpose eq11 eq2211
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq2211
       have r₂ := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq2211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211
  have eq2213 : (k x x) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq2212
  have eq2214 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2213
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq2213
    | exact resolve eq2213 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213
  have eq2215 : (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2214
       have i₂ := eq173 (σ y)
       grind)
    | exact superpose eq173 eq2214
    | exact resolve eq2214 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq2287 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq2215
       grind)
    | exact superpose eq2215 eq10
    | exact resolve eq10 eq2215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2215
  have eq2288 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2287
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2287
    | exact resolve eq2287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2287
  have eq2289 : y = (M.op x y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2288
  have eq2364 : y ≠ y ∨ (M.op y y) = (M.op x x) ∨ x = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2289
       grind)
    | exact superpose eq2289 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2289
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2289
       grind)
    | exact resolve eq13 eq2289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2289
  have eq2366 : (M.op y y) = (M.op x x) ∨ x = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2364
  have eq2367 : (M.op y y) = (k x x) ∨ x = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2366
       have i₂ := eq173 x
       grind)
    | exact superpose eq173 eq2366
    | exact resolve eq2366 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366
  have eq2369 : x = (k y x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2367
       have i₂ := eq173 y
       grind)
    | exact superpose eq173 eq2367
    | exact resolve eq2367 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2367
  have eq2371 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1057 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1057
    | exact resolve eq1057 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2403 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1057 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1057
    | exact resolve eq1057 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq2512 : (k x x) = (k y y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq2369
       grind)
    | exact superpose eq2369 eq10
    | exact resolve eq10 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369
  have eq2586 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq176 x y
       grind)
    | exact superpose eq176 eq9
    | (have j1 := eq176 x y
       grind)
    | exact resolve eq9 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2600 : (k x x) ≠ (k y y) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2586
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq2586
    | exact resolve eq2586 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586
  have eq2825 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq2512
       grind)
    | exact superpose eq2512 eq10
    | exact resolve eq10 eq2512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512
  have eq2829 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2825
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2825
    | exact resolve eq2825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2825
  have eq2830 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2829
  have eq2907 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2830
       grind)
    | exact superpose eq2830 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2830
       grind)
    | exact resolve eq13 eq2830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2830
  have eq2909 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2907
  have eq2910 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2909
  have eq2913 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2910
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq2910
    | exact resolve eq2910 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2910
  have eq2915 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2913
       have i₂ := eq173 (σ y)
       grind)
    | exact superpose eq173 eq2913
    | exact resolve eq2913 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2913
  have eq2916 : x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2915
  have eq2994 : x ≠ x ∨ x = y ∨ (M.op y y) = (M.op x x) ∨ y = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2916
       grind)
    | exact superpose eq2916 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2916
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2916
       grind)
    | exact resolve eq12 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2916
  have eq2996 : x = y ∨ (M.op y y) = (M.op x x) ∨ y = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2994
  have eq2999 : (M.op y y) = (k x x) ∨ x = y ∨ y = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2996
       have i₂ := eq173 x
       grind)
    | exact superpose eq173 eq2996
    | exact resolve eq2996 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996
  have eq3002 : y = (k y x) ∨ x = y ∨ (k x x) = (k y y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2999
       have i₂ := eq173 y
       grind)
    | exact superpose eq173 eq2999
    | exact resolve eq2999 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2999
  have eq3153 : x ≠ (k y x) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k x x) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq2206 x y
       grind)
    | exact superpose eq2206 eq9
    | (have j1 := eq2206 x y
       grind)
    | exact resolve eq9 eq2206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3376 : (k x x) = (k y y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq3002
       grind)
    | exact superpose eq3002 eq10
    | exact resolve eq10 eq3002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002
  have eq3511 : (k (σ y) (σ y)) = (σ (k x x)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq3376
       grind)
    | exact superpose eq3376 eq10
    | exact resolve eq10 eq3376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3376
  have eq3517 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3511
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq3511
    | exact resolve eq3511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3511
  have eq3518 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq3517
  have eq3658 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3518
       grind)
    | exact superpose eq3518 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3518
       grind)
    | exact resolve eq12 eq3518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3518
  have eq3661 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq3658
  have eq3662 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq3661
  have eq3667 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3662
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq3662
    | exact resolve eq3662 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq3671 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3667
       have i₂ := eq173 (σ y)
       grind)
    | exact superpose eq173 eq3667
    | exact resolve eq3667 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3667
  have eq3672 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq3671
  have eq3942 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2600
       have i₂ := eq3672
       grind)
    | exact superpose eq3672 eq2600
    | exact resolve eq2600 eq3672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3672
  have eq3943 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq3942
  have eq3944 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3943
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq3943
    | (have r₁ := eq3943
       have r₂ := eq173 (σ x)
       grind)
    | exact resolve eq3943 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3943
  have eq3945 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq3944
  have eq4224 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq17 y y
       have i₂ := eq3945
       grind)
    | exact superpose eq3945 eq17
    | exact resolve eq17 eq3945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4301 : (k x x) = (k y y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq4224
       have i₂ := eq17 x x
       grind)
    | exact superpose eq17 eq4224
    | exact resolve eq4224 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4224
  have eq4338 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2371 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2371
    | exact resolve eq2371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2371
  have eq4481 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2600
       have i₂ := eq4301
       grind)
    | exact superpose eq4301 eq2600
    | (have r₁ := eq2600
       have r₂ := eq4301
       grind)
    | exact resolve eq2600 eq4301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4487 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq4481
  have eq4640 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq4487
       have i₂ := eq176 (σ x) (σ y)
       grind)
    | exact superpose eq176 eq4487
    | (have j1 := eq176 (σ x) (σ y)
       grind)
    | (have r₁ := eq4487
       have r₂ := eq176 (σ x) (σ y)
       grind)
    | exact resolve eq4487 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4487
  have eq4642 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq4640
  have eq4646 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq4642
       have r₂ := eq3945
       grind)
    | exact resolve eq4642 eq3945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3945 eq4642
  have eq4837 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2403 x (σ y)
       have i₂ := eq4646
       grind)
    | exact superpose eq4646 eq2403
    | exact resolve eq2403 eq4646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403 eq4646
  have eq4841 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq4837
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq4837
    | exact resolve eq4837 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4837
  have eq5013 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (k X0 X0) = (k X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq2207 X1 X0
       grind)
    | exact superpose eq2207 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq2207 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq2207 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq2207 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq2207 X1 X1
       grind)
    | exact resolve eq13 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207
  have eq5020 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (k X0 X0) = (k X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5013 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5013
  have eq5022 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (k X0 X0) = (k X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5020 X0 X1
       have i₂ := eq173 X1
       grind)
    | exact superpose eq173 eq5020
    | (have j0 := eq5020 X0 X1
       grind)
    | exact resolve eq5020 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5020
  have eq5023 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (k X0 X0) = (k X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5022 X0 X1
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq5022
    | (have j0 := eq5022 X0 X1
       grind)
    | exact resolve eq5022 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5022
  have eq5024 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5023 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5023
  have eq13380 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4338 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq4338
    | exact resolve eq4338 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4338
  have eq26393 : y ≠ (k y x) ∨ x = (k y x) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq5024 y x
       grind)
    | exact superpose eq5024 eq9
    | (have j1 := eq5024 y x
       grind)
    | exact resolve eq9 eq5024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26413 : y ≠ y ∨ x = y ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq26393
       have i₂ := eq4841
       grind)
    | exact superpose eq4841 eq26393
    | (have r₁ := eq26393
       have r₂ := eq4841
       grind)
    | exact resolve eq26393 eq4841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4841 eq26393
  have eq26416 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ x = y ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq26413
  have eq26812 : (σ x) ≠ (σ x) ∨ x = y ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq26416
       have i₂ := eq5024 (σ y) (σ x)
       grind)
    | exact superpose eq5024 eq26416
    | (have j1 := eq5024 (σ y) (σ x)
       grind)
    | (have r₁ := eq26416
       have r₂ := eq5024 (σ y) (σ x)
       grind)
    | exact resolve eq26416 eq5024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5024 eq26416
  have eq26817 : (σ x) ≠ (σ x) ∨ x = y ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq26812
  have eq26818 : x = y ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq26817
  have eq26822 : (k x x) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq26818
       have r₂ := eq4301
       grind)
    | exact resolve eq26818 eq4301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4301 eq26818
  have eq27275 : (k (σ y) (σ y)) = (σ (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq26822
       grind)
    | exact superpose eq26822 eq10
    | exact resolve eq10 eq26822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26822
  have eq27281 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq27275
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq27275
    | exact resolve eq27275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27275
  have eq27282 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq27281
  have eq27684 : (k y y) = (τ (k (σ x) (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq17 y y
       have i₂ := eq27282
       grind)
    | exact superpose eq27282 eq17
    | exact resolve eq17 eq27282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27837 : (k x x) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq27684
       have i₂ := eq17 x x
       grind)
    | exact superpose eq17 eq27684
    | exact resolve eq27684 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27684
  have eq28371 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2600
       have i₂ := eq27837
       grind)
    | exact superpose eq27837 eq2600
    | (have r₁ := eq2600
       have r₂ := eq27837
       grind)
    | exact resolve eq2600 eq27837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28377 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq28371
  have eq28791 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq28377
       have i₂ := eq176 (σ x) (σ y)
       grind)
    | exact superpose eq176 eq28377
    | (have j1 := eq176 (σ x) (σ y)
       grind)
    | (have r₁ := eq28377
       have r₂ := eq176 (σ x) (σ y)
       grind)
    | exact resolve eq28377 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28377
  have eq28793 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq28791
  have eq28798 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq28793
       have r₂ := eq27282
       grind)
    | exact resolve eq28793 eq27282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28793
  have eq28845 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13380 y (σ x)
       have i₂ := eq28798
       grind)
    | exact superpose eq28798 eq13380
    | exact resolve eq13380 eq28798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13380 eq28798
  have eq28925 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28845
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq28845
    | exact resolve eq28845 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28845
  have eq29007 : x ≠ x ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k x x) = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3153
       have i₂ := eq28925
       grind)
    | exact superpose eq28925 eq3153
    | (have r₁ := eq3153
       have r₂ := eq28925
       grind)
    | exact resolve eq3153 eq28925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3153
  have eq29013 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k x x) = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29007
  have eq34274 : (σ y) ≠ (σ y) ∨ (k x x) = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29013
       have i₂ := eq2206 (σ x) (σ y)
       grind)
    | exact superpose eq2206 eq29013
    | (have j1 := eq2206 (σ x) (σ y)
       grind)
    | (have r₁ := eq29013
       have r₂ := eq2206 (σ x) (σ y)
       grind)
    | exact resolve eq29013 eq2206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206 eq29013
  have eq34277 : (k x x) = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34274
  have eq34283 : x = (M.op x y) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq34277
       have r₂ := eq27837
       grind)
    | exact resolve eq34277 eq27837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27837 eq34277
  have eq43837 : x ≠ x ∨ x = y ∨ (M.op y y) = (M.op x x) ∨ y = (k y x) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq34283
       grind)
    | exact superpose eq34283 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq34283
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq34283
       grind)
    | exact resolve eq12 eq34283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34283
  have eq43840 : x ≠ x ∨ x = y ∨ (M.op y y) = (M.op x x) ∨ y = (k y x) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43837
  have eq43841 : x = y ∨ (M.op y y) = (M.op x x) ∨ y = (k y x) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43840
  have eq43845 : (M.op y y) = (k x x) ∨ x = y ∨ y = (k y x) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43841
       have i₂ := eq173 x
       grind)
    | exact superpose eq173 eq43841
    | exact resolve eq43841 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43841
  have eq43849 : (k x x) = (k y y) ∨ x = y ∨ y = (k y x) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43845
       have i₂ := eq173 y
       grind)
    | exact superpose eq173 eq43845
    | exact resolve eq43845 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43845
  have eq43850 : (k x x) = (k y y) ∨ x = y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43849
  have eq43853 : (k x x) = (k y y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28925 eq43850
    | exact resolve eq43850 eq28925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28925 eq43850
  have eq43854 : (k x x) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43853
  have eq44399 : (k (σ y) (σ y)) = (σ (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq43854
       grind)
    | exact superpose eq43854 eq10
    | exact resolve eq10 eq43854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43854
  have eq44405 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44399
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq44399
    | exact resolve eq44399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44399
  have eq44406 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq44405
  have eq44918 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq44406
       grind)
    | exact superpose eq44406 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq44406
       grind)
    | exact resolve eq12 eq44406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44406
  have eq44921 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq44918
  have eq44922 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq44921
  have eq44933 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq44922
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq44922
    | exact resolve eq44922 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44922
  have eq44938 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq44933
       have i₂ := eq173 (σ y)
       grind)
    | exact superpose eq173 eq44933
    | exact resolve eq44933 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44933
  have eq44939 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq44938
  have eq44942 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27282 eq44939
    | exact resolve eq44939 eq27282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27282 eq44939
  have eq44943 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq44942
  have eq44948 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17 y y
       have i₂ := eq44943
       grind)
    | exact superpose eq44943 eq17
    | exact resolve eq17 eq44943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45153 : (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq44948
       have i₂ := eq17 x x
       grind)
    | exact superpose eq17 eq44948
    | exact resolve eq44948 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq44948
  have eq45259 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2600
       have i₂ := eq45153
       grind)
    | exact superpose eq45153 eq2600
    | (have r₁ := eq2600
       have r₂ := eq45153
       grind)
    | exact resolve eq2600 eq45153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45153
  have eq45264 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq45259
  have eq45274 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq45264
       have i₂ := eq176 (σ x) (σ y)
       grind)
    | exact superpose eq176 eq45264
    | (have j1 := eq176 (σ x) (σ y)
       grind)
    | (have r₁ := eq45264
       have r₂ := eq176 (σ x) (σ y)
       grind)
    | exact resolve eq45264 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq45264
  have eq45276 : (σ x) = (σ y) ∨ x = y ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq45274
  have eq45280 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq45276
       have r₂ := eq44943
       grind)
    | exact resolve eq45276 eq44943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44943 eq45276
  have eq45286 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2600
       have i₂ := eq45280
       grind)
    | exact superpose eq45280 eq2600
    | exact resolve eq2600 eq45280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45280
  have eq45287 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq45286
  have eq45288 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45287
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq45287
    | (have r₁ := eq45287
       have r₂ := eq173 (σ x)
       grind)
    | exact resolve eq45287 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45287
  have eq45289 : (σ x) = (σ y) := by grind
  clear eq45288
  have eq45300 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq45289
       grind)
    | exact superpose eq45289 eq16
    | exact resolve eq16 eq45289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45289
  have eq45527 : x = y := by
    first
    | (have i₁ := eq45300
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq45300
    | exact resolve eq45300 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45300
  have eq45539 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2600
       have i₂ := eq45527
       grind)
    | exact superpose eq45527 eq2600
    | exact resolve eq2600 eq45527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2600 eq45527
  have eq45540 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq45539
  have eq45541 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq45540
       have i₂ := eq173 (σ x)
       grind)
    | exact superpose eq173 eq45540
    | (have r₁ := eq45540
       have r₂ := eq173 (σ x)
       grind)
    | exact resolve eq45540 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq45540
  have eq45542 : False := by grind
  exact eq45542

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then Y else if m(Y,X) = Y then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyy_pyx_x_pyx_y_pyx_y_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq11 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq14 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq11 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq27 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq11
    | (have j0 := eq11 X1 (σ X0)
       grind)
    | exact resolve eq11 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17 (σ y) (σ x)
       grind)
    | exact superpose eq17 eq16
    | (have j1 := eq17 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq17 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : (M.op (σ x) (σ y)) = (σ (k y (τ (σ x)))) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq35
    | exact resolve eq35 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq41 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq43 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq17 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq17 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq17 X0 X0
       grind)
    | exact resolve eq13 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq45 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq37 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq37 (k X1 X0) X1
       grind)
    | (have r₁ := eq44 X0 X0
       have r₂ := eq37 X0 (k X0 X0)
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq37 X0 X1
       grind)
    | exact resolve eq44 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq45 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq45 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq11 (M.op X1 X1) X1
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq64 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46 (σ x) (σ y)
       grind)
    | exact superpose eq46 eq16
    | (have j1 := eq46 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq46 X1 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq66 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq66 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq66 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq68 : (M.op (σ x) (σ y)) = (σ (k y (τ (σ x)))) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq64
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq64
    | exact resolve eq64 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq70 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq68
    | exact resolve eq68 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq71 : (σ y) = (σ (k y (τ (σ x)))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq70
    | exact resolve eq70 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq71
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq82 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41
       have i₂ := eq17 y x
       grind)
    | exact superpose eq17 eq41
    | (have j1 := eq17 y x
       grind)
    | exact resolve eq41 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq82
  have eq84 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ (k X0 (τ X1))) = X1 ∨ (σ X0) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X1) X0
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq67
    | exact resolve eq67 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (τ (k X0 (σ X1))) = X1 ∨ (τ X0) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (τ X0) X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq67
    | exact resolve eq67 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) := by
    intro X0
    first
    | (have j0 := eq27 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq101 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq101
    | exact resolve eq101 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq109 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) ≠ (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq102
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq9
    | exact resolve eq9 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq116 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq109 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq129 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq115 X0
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq115
    | exact resolve eq115 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq130 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X1
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq27
    | (have j0 := eq27 X0 X1
       grind)
    | exact resolve eq27 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq140 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq129 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq129
    | exact resolve eq129 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq157 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq22 X0 (τ X0)
       have i₂ := eq140 (τ X0)
       grind)
    | exact superpose eq140 eq22
    | exact resolve eq22 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq157 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq157
    | exact resolve eq157 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq162 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq158 X0
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq158
    | exact resolve eq158 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq158
  have eq168 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq72
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq72 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : y = (k y x) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq168
  have eq178 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 (τ (σ X0)))) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq130 X1 (σ X0)
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq130
    | (have j0 := eq130 X1 (σ X0)
       grind)
    | (have r₁ := eq130 X0 (σ X0)
       have r₂ := eq116 X0
       grind)
    | exact resolve eq130 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq178
    | (have j0 := eq178 X0 X1
       grind)
    | exact resolve eq178 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq255 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq84
    | exact resolve eq84 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ (k X1 (τ X0))) = X0 ∨ (σ X1) = (σ (k X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 (τ X0))
       have i₂ := eq84 X1 X0
       grind)
    | exact superpose eq84 eq9
    | (have j1 := eq84 X1 X0
       grind)
    | exact resolve eq9 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq294 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) ∨ (τ X0) = (τ (k X1 X0)) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq334 : y ≠ (M.op x y) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  have eq498 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq255 X1 X0
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq255
    | (have j1 := eq67 X1 X0
       grind)
    | exact resolve eq255 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq255 x y
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq255
    | (have j0 := eq255 x y
       grind)
    | exact resolve eq255 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq255 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq517 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq503
       have r₂ := eq16
       grind)
    | exact resolve eq503 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq519 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq517
       have r₂ := eq41
       grind)
    | exact resolve eq517 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq552 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (k X1 X0)) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq294 X0 X1
       grind)
    | exact superpose eq294 eq10
    | (have j1 := eq294 X0 X1
       grind)
    | exact resolve eq10 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 : G, (τ X1) ≠ (M.op (τ X1) (τ X0)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq294 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X1) (τ X0)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq294 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq590 : ∀ X0 X1 : G, (σ (σ X0)) = (σ (σ (k X0 (τ (τ X1))))) ∨ (σ (σ (k X0 (τ (τ X1))))) = X1 ∨ (σ (k X0 (τ (τ X1)))) = (τ (M.op X1 (σ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq263 X0 (σ X1)
       have i₂ := eq19 (τ X0) X1
       grind)
    | exact superpose eq19 eq263
    | exact resolve eq263 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq2296 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq519
       grind)
    | exact superpose eq519 eq72
    | (have r₁ := eq72
       have r₂ := eq519
       grind)
    | exact resolve eq72 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq2304 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2296
  have eq2305 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2304
  have eq2308 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq2305
       have r₂ := eq72
       grind)
    | exact resolve eq2305 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq2305
  have eq2659 : ∀ X0 X1 : G, (σ (k X0 (τ (τ X1)))) = (τ (σ (σ X0))) ∨ (σ (σ (k X0 (τ (τ X1))))) = X1 ∨ (σ (k X0 (τ (τ X1)))) = (τ (M.op X1 (σ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ (k X0 (τ (τ X1))))
       have i₂ := eq590 X0 X1
       grind)
    | exact superpose eq590 eq9
    | (have j1 := eq590 X0 X1
       grind)
    | exact resolve eq9 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq2691 : ∀ X0 X1 : G, (σ (σ (k X0 (τ (τ X1))))) = X1 ∨ (σ X0) = (σ (k X0 (τ (τ X1)))) ∨ (σ (k X0 (τ (τ X1)))) = (τ (M.op X1 (σ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2659 X0 X1
       have i₂ := eq9 (σ X0)
       grind)
    | exact superpose eq9 eq2659
    | (have j0 := eq2659 X0 X1
       grind)
    | exact resolve eq2659 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2659
  have eq3213 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X0) ∨ (σ X1) = (σ (M.op X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0)
       have i₂ := eq498 X1 X0
       grind)
    | exact superpose eq498 eq9
    | (have j1 := eq498 X1 X0
       grind)
    | exact resolve eq9 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq3267 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (σ X1) = (σ (M.op X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3213 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3213
    | (have j0 := eq3213 X0 X1
       grind)
    | exact resolve eq3213 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3213
  have eq3271 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3267 X0 X1
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq3267 X0 X1
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq3267 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3267
  have eq6890 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1)
       have i₂ := eq3271 X1 X0
       grind)
    | exact superpose eq3271 eq9
    | (have j1 := eq3271 X1 X0
       grind)
    | exact resolve eq9 eq3271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271
  have eq6961 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6890 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6890
    | (have j0 := eq6890 X0 X1
       grind)
    | exact resolve eq6890 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6890
  have eq6967 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6961 X0 X1
       have j1 := eq88 X1 X0
       grind)
    | (have r₁ := eq6961 X1 X0
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq6961 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6961
  have eq7004 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (M.op (σ X1) (σ (σ X0))) = (σ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6967 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq6967
    | (have j0 := eq6967 X1 (σ X0)
       grind)
    | exact resolve eq6967 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7005 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (σ X1))) ∨ (τ (k X0 (σ X1))) = X1 ∨ (M.op (σ X1) (σ (τ X0))) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6967 X1 (τ X0)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq6967
    | (have j0 := eq6967 X1 (τ X0)
       grind)
    | exact resolve eq6967 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7013 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83
       have i₂ := eq6967 x y
       grind)
    | exact superpose eq6967 eq83
    | (have j1 := eq6967 x y
       grind)
    | exact resolve eq83 eq6967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7015 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq7013
  have eq7018 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have r₁ := eq7015
       have r₂ := eq16
       grind)
    | exact resolve eq7015 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7015
  have eq7023 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (σ X1))) ∨ (M.op (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7005 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7005
    | (have j0 := eq7005 X0 X1
       grind)
    | exact resolve eq7005 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7005
  have eq7527 : y ≠ y ∨ x = (k y x) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq7018
       grind)
    | exact superpose eq7018 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq7018
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq7018
       grind)
    | exact resolve eq12 eq7018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7529 : y ≠ y ∨ x = (k y x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq89 y x
       have i₂ := eq7018
       grind)
    | exact superpose eq7018 eq89
    | (have j0 := eq89 y x
       grind)
    | (have r₁ := eq89 y x
       have r₂ := eq7018
       grind)
    | (have r₁ := eq89 (σ y) (σ x)
       have r₂ := eq7018
       grind)
    | exact resolve eq89 eq7018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7018
  have eq7532 : y ≠ y ∨ x = (k y x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7529
  have eq7533 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = (k y x) := by grind
  clear eq7532
  have eq7535 : y ≠ y ∨ x = (k y x) ∨ (M.op y y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7527
  have eq7536 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ x = (k y x) := by grind
  clear eq7535
  have eq7640 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7533
       grind)
    | exact superpose eq7533 eq16
    | exact resolve eq16 eq7533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7641 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq513 y x
       have i₂ := eq7533
       grind)
    | exact superpose eq7533 eq513
    | (have j0 := eq513 y x
       grind)
    | (have r₁ := eq513 y x
       have r₂ := eq7533
       grind)
    | exact resolve eq513 eq7533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq7533
  have eq7655 : y = (k y x) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (k y x) := by grind
  clear eq7641
  have eq7945 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op y y) = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7536
       grind)
    | exact superpose eq7536 eq16
    | exact resolve eq16 eq7536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7953 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq7536
       grind)
    | exact superpose eq7536 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq7536
       grind)
    | exact resolve eq12 eq7536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7960 : (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ x = (k y x) := by grind
  clear eq7953
  have eq7968 : (σ x) = (σ (k y (τ (σ x)))) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq7960
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq7960
    | exact resolve eq7960 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7960
  have eq7979 : (σ x) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq7968
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq7968
    | exact resolve eq7968 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7968
  have eq7988 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ (M.op y y) = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq7979
       have i₂ := eq116 x
       grind)
    | exact superpose eq116 eq7979
    | exact resolve eq7979 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7979
  have eq7995 : x = (k y x) ∨ (σ x) = (σ (k y x)) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq7988
       have i₂ := eq116 y
       grind)
    | exact superpose eq116 eq7988
    | exact resolve eq7988 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7988
  have eq8121 : (σ x) ≠ (σ y) ∨ (M.op y y) = (M.op x x) ∨ x = (k y x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7945
       have i₂ := eq17 y x
       grind)
    | exact superpose eq17 eq7945
    | (have j1 := eq17 y x
       grind)
    | exact resolve eq7945 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7945
  have eq8131 : (σ x) ≠ (σ y) ∨ (M.op y y) = (M.op x x) ∨ x = (k y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq8121
       have r₂ := eq12 y x
       grind)
    | exact resolve eq8121 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8121
  have eq8132 : (σ x) ≠ (σ y) ∨ x = (k y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq11 y x
       grind)
    | (have r₁ := eq8131
       have r₂ := eq11 y x
       grind)
    | (have r₁ := eq8131
       have r₂ := eq11 x y
       grind)
    | exact resolve eq8131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8131
  have eq8628 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq7655
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq7655
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq7655 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq7655
  have eq8638 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (k y x) ∨ y = (k y x) := by
    first
    | (have j1 := eq89 y x
       grind)
    | (have r₁ := eq8628
       have r₂ := eq89 y x
       grind)
    | exact resolve eq8628 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq8628
  have eq8640 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y x) ∨ y = (k y x) := by
    first
    | (have j1 := eq88 y x
       grind)
    | (have r₁ := eq8638
       have r₂ := eq88 y x
       grind)
    | exact resolve eq8638 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8638
  have eq8642 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq8640
       have r₂ := eq7640
       grind)
    | exact resolve eq8640 eq7640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7640 eq8640
  have eq8728 : (M.op x y) = (τ (σ x)) ∨ x = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq8642
       grind)
    | exact superpose eq8642 eq9
    | exact resolve eq9 eq8642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8642
  have eq8772 : x = (M.op x y) ∨ x = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq8728
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq8728
    | exact resolve eq8728 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8728
  have eq8775 : y = (k y x) ∨ x = (k y x) := by
    first
    | (have j1 := eq88 y x
       grind)
    | (have r₁ := eq8772
       have r₂ := eq88 y x
       grind)
    | exact resolve eq8772 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq8772
  have eq9069 : (M.op y y) ≠ (M.op x x) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq8775
       grind)
    | exact superpose eq8775 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq8775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9070 : x ≠ y ∨ x = (k y x) := by grind
  have eq10471 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (σ X1))
       have i₂ := eq7023 X0 X1
       grind)
    | exact superpose eq7023 eq10
    | (have j1 := eq7023 X0 X1
       grind)
    | exact resolve eq10 eq7023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7023
  have eq10519 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10471 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10471
    | (have j0 := eq10471 X0 X1
       grind)
    | exact resolve eq10471 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10471
  have eq10837 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10519 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10519
    | exact resolve eq10519 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10869 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (τ (σ X1)))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10519 (σ X1) X1
       have i₂ := eq19 (σ X1) X1
       grind)
    | exact superpose eq19 eq10519
    | (have j0 := eq10519 (σ X0) X1
       grind)
    | exact resolve eq10519 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10519
  have eq10880 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10869 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq10869
    | (have j0 := eq10869 X0 X1
       grind)
    | exact resolve eq10869 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10869
  have eq10889 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10880 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq10880
    | (have j0 := eq10880 X0 X1
       grind)
    | exact resolve eq10880 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10880
  have eq10893 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = X1 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10889 X0 X1
       have i₂ := eq9 (k X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq10889
    | (have j0 := eq10889 X0 X1
       grind)
    | exact resolve eq10889 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10889
  have eq10896 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10893 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq10893
    | (have j0 := eq10893 X0 X1
       grind)
    | exact resolve eq10893 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10893
  have eq11069 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq10837 X0 X1
       grind)
    | exact superpose eq10837 eq10
    | (have j1 := eq10837 X0 X1
       grind)
    | exact resolve eq10 eq10837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10837
  have eq11121 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11069 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11069
    | (have j0 := eq11069 X0 X1
       grind)
    | exact resolve eq11069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11069
  have eq11262 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (τ X1))) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11121 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq11121
    | (have j0 := eq11121 X1 (σ X0)
       grind)
    | exact resolve eq11121 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11121
  have eq11280 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (σ X0) = (σ (k X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11262 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11262
    | (have j0 := eq11262 X0 X1
       grind)
    | exact resolve eq11262 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11262
  have eq13157 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11280 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11280
    | exact resolve eq11280 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11280
  have eq13585 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq13157 X1 X0
       grind)
    | exact superpose eq13157 eq9
    | (have j1 := eq13157 X1 X0
       grind)
    | exact resolve eq9 eq13157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13636 : ∀ X0 X1 : G, (σ X0) ≠ (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq13157 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13157
  have eq13640 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13585 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13585
    | (have j0 := eq13585 X0 X1
       grind)
    | exact resolve eq13585 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13585
  have eq14587 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13640 y x
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq13640
    | (have j0 := eq13640 y x
       grind)
    | exact resolve eq13640 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq14596 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq14587
  have eq14600 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq14596
       have r₂ := eq16
       grind)
    | exact resolve eq14596 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14596
  have eq14604 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq14600
       have r₂ := eq41
       grind)
    | exact resolve eq14600 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14600
  have eq15639 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq41
       have i₂ := eq14604
       grind)
    | exact superpose eq14604 eq41
    | exact resolve eq41 eq14604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq14604
  have eq15660 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15639
  have eq25072 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ (k X0 (τ X1))) = X1 ∨ (M.op (σ X1) (σ (σ X0))) = (σ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq7004 X0 X1
       grind)
    | exact superpose eq7004 eq9
    | (have j1 := eq7004 X0 X1
       grind)
    | exact resolve eq9 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7004
  have eq25147 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ (k X0 (τ X1))) = X1 ∨ (M.op (σ X1) (σ (σ X0))) = (σ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25072 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq25072
    | (have j0 := eq25072 X0 X1
       grind)
    | exact resolve eq25072 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25072
  have eq25943 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (σ (τ X1)))) ∨ (σ (τ (k X0 (σ (τ X1))))) = X1 ∨ (M.op (σ X1) (σ (σ (τ X0)))) = (σ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25147 (τ X0) X1
       have i₂ := eq22 X0 (τ X1)
       grind)
    | exact superpose eq22 eq25147
    | (have j0 := eq25147 (τ X0) X1
       grind)
    | exact resolve eq25147 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25147
  have eq25957 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ (k X0 (σ (τ X1))))) = X1 ∨ (M.op (σ X1) (σ (σ (τ X0)))) = (σ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25943 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq25943
    | (have j0 := eq25943 X0 X1
       grind)
    | exact resolve eq25943 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25943
  have eq25971 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (M.op (σ X1) (σ (σ (τ X0)))) = (σ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25957 X0 X1
       have i₂ := eq10 (k X0 (σ (τ X1)))
       grind)
    | exact superpose eq10 eq25957
    | (have j0 := eq25957 X0 X1
       grind)
    | exact resolve eq25957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25957
  have eq25976 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (M.op (σ X1) (σ (σ (τ X0)))) = (σ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25971 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq25971
    | (have j0 := eq25971 X0 X1
       grind)
    | exact resolve eq25971 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25971
  have eq25981 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25976 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25976
    | (have j0 := eq25976 X0 X1
       grind)
    | exact resolve eq25976 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25976
  have eq26226 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = X1 ∨ (M.op (σ X1) (σ (τ X0))) = (σ (M.op X1 (τ X0))) ∨ (τ (τ X0)) = (τ (τ (k X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25981 (τ X0) X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq25981
    | (have j0 := eq25981 (τ X0) X1
       grind)
    | exact resolve eq25981 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25981
  have eq26335 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = X1 ∨ (M.op (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ (τ X0)) = (τ (τ (k X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq26226 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26226
    | (have j0 := eq26226 X0 X1
       grind)
    | exact resolve eq26226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26226
  have eq28811 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (k X1 X0)) ∨ (τ (τ X1)) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26335 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26335
    | exact resolve eq26335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26335
  have eq29306 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = (τ (k (σ X0) X1)) ∨ (τ X0) = (τ (τ (k (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28811 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq28811
    | (have j0 := eq28811 X1 (σ X0)
       grind)
    | exact resolve eq28811 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28811
  have eq29528 : ∀ X0 X1 : G, (τ X1) = (τ (σ (k X0 (τ X1)))) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X0) = (τ (τ (k (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29306 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq29306
    | (have j0 := eq29306 X0 X1
       grind)
    | exact resolve eq29306 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29306
  have eq29565 : ∀ X0 X1 : G, (τ X1) = (k X0 (τ X1)) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X0) = (τ (τ (k (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29528 X0 X1
       have i₂ := eq9 (k X0 (τ X1))
       grind)
    | exact superpose eq9 eq29528
    | (have j0 := eq29528 X0 X1
       grind)
    | exact resolve eq29528 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29528
  have eq29598 : ∀ X0 X1 : G, (τ X0) = (τ (τ (σ (k X0 (τ X1))))) ∨ (τ X1) = (k X0 (τ X1)) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29565 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq29565
    | (have j0 := eq29565 X0 X1
       grind)
    | exact resolve eq29565 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29565
  have eq29613 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = (k X0 (τ X1)) ∨ (τ X0) = (τ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29598 X0 X1
       have i₂ := eq9 (k X0 (τ X1))
       grind)
    | exact superpose eq9 eq29598
    | (have j0 := eq29598 X0 X1
       grind)
    | exact resolve eq29598 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29598
  have eq29819 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ X0)) ∨ (M.op (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (τ X1) = (τ (k X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (τ X0) X1)
       have i₂ := eq29613 X1 X0
       grind)
    | exact superpose eq29613 eq9
    | (have j1 := eq29613 X1 X0
       grind)
    | exact resolve eq9 eq29613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29613
  have eq30273 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29819 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq29819
    | exact resolve eq29819 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29819
  have eq30728 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = X1 ∨ (M.op X1 (τ X0)) = (τ (M.op (σ X1) (σ (τ X0)))) ∨ (τ (τ X0)) = (τ (τ (k X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30273 X1 (τ X0)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq30273
    | (have j0 := eq30273 X1 (τ X0)
       grind)
    | exact resolve eq30273 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30273
  have eq30844 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (τ (k X0 (σ X1))) = X1 ∨ (τ (τ X0)) = (τ (τ (k X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30728 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30728
    | (have j0 := eq30728 X0 X1
       grind)
    | exact resolve eq30728 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30728
  have eq44516 : (τ (σ y)) = (M.op x (τ (σ y))) ∨ x = (τ (k (σ y) (σ x))) ∨ (τ (τ (σ y))) = (τ (τ (k (σ y) (σ x)))) ∨ (M.op y y) = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq30844 (σ y) x
       have i₂ := eq7536
       grind)
    | exact superpose eq7536 eq30844
    | (have j0 := eq30844 (σ y) x
       grind)
    | exact resolve eq30844 eq7536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7536 eq30844
  have eq44672 : y = (M.op x y) ∨ x = (τ (k (σ y) (σ x))) ∨ (τ (τ (σ y))) = (τ (τ (k (σ y) (σ x)))) ∨ (M.op y y) = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq44516
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq44516
    | exact resolve eq44516 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44516
  have eq44712 : y = (M.op x y) ∨ x = (τ (k (σ y) (σ x))) ∨ (τ (τ (σ y))) = (τ (τ (k (σ y) (σ x)))) ∨ x = (k y x) := by
    first
    | (have r₁ := eq44672
       have r₂ := eq9069
       grind)
    | exact resolve eq44672 eq9069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9069 eq44672
  have eq44735 : x = (τ (σ (k y (τ (σ x))))) ∨ y = (M.op x y) ∨ (τ (τ (σ y))) = (τ (τ (k (σ y) (σ x)))) ∨ x = (k y x) := by
    first
    | (have i₁ := eq44712
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq44712
    | exact resolve eq44712 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44712
  have eq44757 : x = (k y (τ (σ x))) ∨ y = (M.op x y) ∨ (τ (τ (σ y))) = (τ (τ (k (σ y) (σ x)))) ∨ x = (k y x) := by
    first
    | (have i₁ := eq44735
       have i₂ := eq9 (k y (τ (σ x)))
       grind)
    | exact superpose eq9 eq44735
    | exact resolve eq44735 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44735
  have eq44769 : x = (k y x) ∨ y = (M.op x y) ∨ (τ (τ (σ y))) = (τ (τ (k (σ y) (σ x)))) ∨ x = (k y x) := by
    first
    | (have i₁ := eq44757
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq44757
    | exact resolve eq44757 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44757
  have eq44770 : x = (k y x) ∨ y = (M.op x y) ∨ (τ (τ (σ y))) = (τ (τ (k (σ y) (σ x)))) := by grind
  clear eq44769
  have eq44773 : (τ (τ (σ y))) = (τ (τ (σ (k y (τ (σ x)))))) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44770
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq44770
    | exact resolve eq44770 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44770
  have eq44776 : (τ (τ (σ y))) = (τ (k y (τ (σ x)))) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44773
       have i₂ := eq9 (k y (τ (σ x)))
       grind)
    | exact superpose eq9 eq44773
    | exact resolve eq44773 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44773
  have eq44779 : (τ (k y x)) = (τ (τ (σ y))) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44776
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq44776
    | exact resolve eq44776 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44776
  have eq44781 : y = (M.op x y) ∨ x = (k y x) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq44779
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq44779
    | exact resolve eq44779 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44779
  have eq45211 : ∀ X0 X1 : G, (σ (σ (τ (k X0 (σ (τ (τ X1))))))) = X1 ∨ (σ (τ X0)) = (σ (τ (k X0 (σ (τ (τ X1)))))) ∨ (σ (τ (k X0 (σ (τ (τ X1)))))) = (τ (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2691 (τ X0) X1
       have i₂ := eq22 X0 (τ (τ X1))
       grind)
    | exact superpose eq22 eq2691
    | exact resolve eq2691 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2691
  have eq45331 : ∀ X0 X1 : G, (σ (k X0 (σ (τ (τ X1))))) = X1 ∨ (σ (τ X0)) = (σ (τ (k X0 (σ (τ (τ X1)))))) ∨ (σ (τ (k X0 (σ (τ (τ X1)))))) = (τ (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq45211 X0 X1
       have i₂ := eq10 (k X0 (σ (τ (τ X1))))
       grind)
    | exact superpose eq10 eq45211
    | (have j0 := eq45211 X0 X1
       grind)
    | exact resolve eq45211 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45211
  have eq45376 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = X1 ∨ (σ (τ X0)) = (σ (τ (k X0 (σ (τ (τ X1)))))) ∨ (σ (τ (k X0 (σ (τ (τ X1)))))) = (τ (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq45331 X0 X1
       have i₂ := eq10 (τ X1)
       grind)
    | exact superpose eq10 eq45331
    | (have j0 := eq45331 X0 X1
       grind)
    | exact resolve eq45331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45331
  have eq45386 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ (τ X1)))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (σ (τ (k X0 (σ (τ (τ X1)))))) = (τ (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq45376 X0 X1
       have i₂ := eq10 (k X0 (σ (τ (τ X1))))
       grind)
    | exact superpose eq10 eq45376
    | (have j0 := eq45376 X0 X1
       grind)
    | exact resolve eq45376 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45376
  have eq45392 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (τ X1)) ∨ (σ (k X0 (τ X1))) = X1 ∨ (σ (τ (k X0 (σ (τ (τ X1)))))) = (τ (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq45386 X0 X1
       have i₂ := eq10 (τ X1)
       grind)
    | exact superpose eq10 eq45386
    | (have j0 := eq45386 X0 X1
       grind)
    | exact resolve eq45386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45386
  have eq45396 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ (k X0 (τ X1))) = X1 ∨ (σ (τ (k X0 (σ (τ (τ X1)))))) = (τ (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq45392 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45392
    | (have j0 := eq45392 X0 X1
       grind)
    | exact resolve eq45392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45392
  have eq45399 : ∀ X0 X1 : G, (τ (M.op X1 (σ X0))) = (σ (τ (k X0 (σ (τ (τ X1)))))) ∨ (k X0 (τ X1)) = X0 ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45396 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45396
    | (have j0 := eq45396 X0 X1
       grind)
    | exact resolve eq45396 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45396
  have eq45402 : ∀ X0 X1 : G, (τ (M.op X1 (σ X0))) = (k X0 (σ (τ (τ X1)))) ∨ (k X0 (τ X1)) = X0 ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45399 X0 X1
       have i₂ := eq10 (k X0 (σ (τ (τ X1))))
       grind)
    | exact superpose eq10 eq45399
    | (have j0 := eq45399 X0 X1
       grind)
    | exact resolve eq45399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45399
  have eq45405 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (k X0 (τ X1)) = X0 ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45402 X0 X1
       have i₂ := eq10 (τ X1)
       grind)
    | exact superpose eq10 eq45402
    | (have j0 := eq45402 X0 X1
       grind)
    | exact resolve eq45402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45402
  have eq45560 : ∀ X0 X1 : G, (τ (M.op X1 (σ X0))) ≠ X0 ∨ (k X0 (τ X1)) = X0 ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45405 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45405
  have eq45772 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (σ (k (τ X0) (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45560 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45560
    | (have j0 := eq45560 (τ X0) X1
       grind)
    | exact resolve eq45560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45560
  have eq45824 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (σ (τ X1)))) ∨ (τ X0) ≠ (τ (M.op X1 X0)) ∨ (σ (k (τ X0) (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45772 X0 X1
       have i₂ := eq22 X0 (τ X1)
       grind)
    | exact superpose eq22 eq45772
    | (have j0 := eq45772 X0 X1
       grind)
    | exact resolve eq45772 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45772
  have eq45838 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ X0) ≠ (τ (M.op X1 X0)) ∨ (σ (k (τ X0) (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45824 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq45824
    | (have j0 := eq45824 X0 X1
       grind)
    | exact resolve eq45824 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45824
  have eq45851 : ∀ X0 X1 : G, (σ (τ (k X0 (σ (τ X1))))) = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ X0) ≠ (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq45838 X0 X1
       have i₂ := eq22 X0 (τ X1)
       grind)
    | exact superpose eq22 eq45838
    | (have j0 := eq45838 X0 X1
       grind)
    | exact resolve eq45838 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45838
  have eq45854 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ X0) ≠ (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq45851 X0 X1
       have i₂ := eq10 (k X0 (σ (τ X1)))
       grind)
    | exact superpose eq10 eq45851
    | (have j0 := eq45851 X0 X1
       grind)
    | exact resolve eq45851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45851
  have eq45857 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45854 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq45854
    | (have j0 := eq45854 X0 X1
       grind)
    | exact resolve eq45854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45854
  have eq46124 : (τ y) ≠ (τ y) ∨ (τ y) = (τ (k y x)) ∨ x = (k y x) ∨ x = (k y x) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq45857 y x
       have i₂ := eq44781
       grind)
    | exact superpose eq44781 eq45857
    | (have j0 := eq45857 y x
       grind)
    | exact resolve eq45857 eq44781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44781 eq45857
  have eq46140 : (τ y) ≠ (τ y) ∨ (τ y) = (τ (k y x)) ∨ x = (k y x) := by grind
  clear eq46124
  have eq46141 : x = (k y x) ∨ (τ y) = (τ (k y x)) := by grind
  clear eq46140
  have eq46411 : x = (σ (M.op (τ x) (τ y))) ∨ (τ y) = (τ (σ (M.op (τ x) (τ y)))) ∨ (τ x) = (τ (k y x)) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq46141
       have i₂ := eq552 x y
       grind)
    | exact superpose eq552 eq46141
    | (have j1 := eq552 x y
       grind)
    | exact resolve eq46141 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq46141
  have eq46415 : (τ y) = (M.op (τ x) (τ y)) ∨ x = (σ (M.op (τ x) (τ y))) ∨ (τ x) = (τ (k y x)) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq46411
       have i₂ := eq9 (M.op (τ x) (τ y))
       grind)
    | exact superpose eq9 eq46411
    | exact resolve eq46411 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46411
  have eq46417 : x = (σ (M.op (τ x) (τ y))) ∨ (τ x) = (τ (k y x)) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have j1 := eq554 y x
       grind)
    | (have r₁ := eq46415
       have r₂ := eq554 y x
       grind)
    | exact resolve eq46415 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq46415
  have eq47351 : (τ x) = (M.op (τ x) (τ y)) ∨ (τ x) = (τ (k y x)) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq9 (M.op (τ x) (τ y))
       have i₂ := eq46417
       grind)
    | exact superpose eq46417 eq9
    | exact resolve eq9 eq46417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46417
  have eq47418 : (τ y) = (τ (k y x)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have j1 := eq553 y x
       grind)
    | (have r₁ := eq47351
       have r₂ := eq553 y x
       grind)
    | exact resolve eq47351 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq47351
  have eq47858 : (k y x) = (σ (τ y)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq47418
       grind)
    | exact superpose eq47418 eq10
    | exact resolve eq10 eq47418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47861 : (τ (M.op (k y x) (k y x))) = (M.op (τ y) (τ y)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq162 (k y x)
       have i₂ := eq47418
       grind)
    | exact superpose eq47418 eq162
    | exact resolve eq162 eq47418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47418
  have eq47944 : (τ x) = (τ (k y x)) ∨ (τ (M.op (k y x) (k y x))) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq47861
       have i₂ := eq162 y
       grind)
    | exact superpose eq162 eq47861
    | exact resolve eq47861 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47861
  have eq47946 : y = (k y x) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq47858
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq47858
    | exact resolve eq47858 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47858
  have eq48719 : (τ (M.op (k y x) (k y x))) = (M.op (τ x) (τ x)) ∨ (τ (M.op (k y x) (k y x))) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq162 (k y x)
       have i₂ := eq47944
       grind)
    | exact superpose eq47944 eq162
    | exact resolve eq162 eq47944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47944
  have eq48793 : (τ (M.op (k y x) (k y x))) = (τ (M.op y y)) ∨ (τ (M.op (k y x) (k y x))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq48719
       have i₂ := eq162 x
       grind)
    | exact superpose eq162 eq48719
    | exact resolve eq48719 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48719
  have eq49904 : (τ (M.op y y)) ≠ (τ (M.op x x)) ∨ (τ (M.op (k y x) (k y x))) = (τ (M.op x x)) := by grind
  clear eq48793
  have eq58114 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq7995
       have i₂ := eq8775
       grind)
    | exact superpose eq8775 eq7995
    | exact resolve eq7995 eq8775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58132 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq7995
       have i₂ := eq13640 y x
       grind)
    | exact superpose eq13640 eq7995
    | (have j1 := eq13640 y x
       grind)
    | exact resolve eq7995 eq13640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7995
  have eq58146 : x = y ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have j1 := eq13636 y x
       grind)
    | (have r₁ := eq58132
       have r₂ := eq13636 x y
       grind)
    | (have r₁ := eq58132
       have r₂ := eq13636 y x
       grind)
    | (have r₁ := eq58132
       have r₂ := eq13636 (M.op x x) (M.op y y)
       grind)
    | exact resolve eq58132 eq13636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13636 eq58132
  have eq58157 : (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (k y x) := by
    first
    | (have r₁ := eq58114
       have r₂ := eq9070
       grind)
    | exact resolve eq58114 eq9070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9070 eq58114
  have eq58161 : x = y ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq58146
       have r₂ := eq16
       grind)
    | exact resolve eq58146 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58146
  have eq58178 : (σ x) ≠ (σ x) ∨ x = (k y x) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq8132
       have i₂ := eq58157
       grind)
    | exact superpose eq58157 eq8132
    | (have r₁ := eq8132
       have r₂ := eq58157
       grind)
    | exact resolve eq8132 eq58157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8132 eq58157
  have eq58250 : (σ x) ≠ (σ x) ∨ x = (k y x) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq58178
  have eq58251 : x = (k y x) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq58250
  have eq58263 : x = (k y x) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have j1 := eq11 y x
       grind)
    | (have r₁ := eq58251
       have r₂ := eq11 y x
       grind)
    | (have r₁ := eq58251
       have r₂ := eq11 x y
       grind)
    | exact resolve eq58251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58251
  have eq58335 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq58263
       have i₂ := eq170
       grind)
    | exact superpose eq170 eq58263
    | exact resolve eq58263 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq58263
  have eq58387 : y = (M.op x y) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j1 := eq37 x y
       grind)
    | (have r₁ := eq58335
       have r₂ := eq37 x y
       grind)
    | (have r₁ := eq58335
       have r₂ := eq37 y x
       grind)
    | (have r₁ := eq58335
       have r₂ := eq37 y (M.op x y)
       grind)
    | exact resolve eq58335 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq58335
  have eq58389 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq58387
       have r₂ := eq334
       grind)
    | exact resolve eq58387 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq58387
  have eq58390 : (M.op x y) = (k y x) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j1 := eq180 x y
       grind)
    | (have r₁ := eq58389
       have r₂ := eq180 x y
       grind)
    | (have r₁ := eq58389
       have r₂ := eq180 y x
       grind)
    | exact resolve eq58389 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq58389
  have eq58598 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq58390
       have i₂ := eq10896 y x
       grind)
    | exact superpose eq10896 eq58390
    | (have j1 := eq10896 y x
       grind)
    | exact resolve eq58390 eq10896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10896
  have eq58708 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq58598
       have r₂ := eq16
       grind)
    | exact resolve eq58598 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58598
  have eq59063 : x ≠ x ∨ y = (k y x) ∨ x = y ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq58708
       grind)
    | exact superpose eq58708 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq58708
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq58708
       grind)
    | exact resolve eq13 eq58708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58708
  have eq59070 : y = (k y x) ∨ x = y ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq59063
  have eq61253 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58161
       grind)
    | exact superpose eq58161 eq16
    | exact resolve eq16 eq58161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58161
  have eq61464 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq61253
       have r₂ := eq116 x
       grind)
    | exact resolve eq61253 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61253
  have eq61542 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq61464
       grind)
    | exact superpose eq61464 eq9
    | exact resolve eq9 eq61464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61464
  have eq61600 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq61542
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq61542
    | exact resolve eq61542 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61542
  have eq61601 : (σ x) = (σ (k y x)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq61600
  have eq61755 : (τ (σ x)) = (k y x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq61601
       grind)
    | exact superpose eq61601 eq9
    | exact resolve eq9 eq61601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61601
  have eq61854 : x = (k y x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq61755
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq61755
    | exact resolve eq61755 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61755
  have eq61990 : x = y ∨ (M.op y y) = (M.op x x) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq61854
       have i₂ := eq47946
       grind)
    | exact superpose eq47946 eq61854
    | exact resolve eq61854 eq47946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47946 eq61854
  have eq62148 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61990
       grind)
    | exact superpose eq61990 eq16
    | exact resolve eq16 eq61990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61990
  have eq62391 : (M.op y y) = (M.op x x) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have r₁ := eq62148
       have r₂ := eq116 x
       grind)
    | exact resolve eq62148 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62148
  have eq62484 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (τ (M.op (k y x) (k y x))) = (τ (M.op x x)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq49904
       have i₂ := eq62391
       grind)
    | exact superpose eq62391 eq49904
    | exact resolve eq49904 eq62391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49904 eq62391
  have eq62811 : (τ x) = (τ (k y x)) ∨ (τ (M.op (k y x) (k y x))) = (τ (M.op x x)) := by grind
  clear eq62484
  have eq65673 : (τ (M.op (k y x) (k y x))) = (M.op (τ x) (τ x)) ∨ (τ (M.op (k y x) (k y x))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq162 (k y x)
       have i₂ := eq62811
       grind)
    | exact superpose eq62811 eq162
    | exact resolve eq162 eq62811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62811
  have eq65736 : (τ (M.op (k y x) (k y x))) = (τ (M.op x x)) ∨ (τ (M.op (k y x) (k y x))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq65673
       have i₂ := eq162 x
       grind)
    | exact superpose eq162 eq65673
    | exact resolve eq65673 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq65673
  have eq65737 : (τ (M.op (k y x) (k y x))) = (τ (M.op x x)) := by grind
  clear eq65736
  have eq65978 : (M.op (k y x) (k y x)) = (σ (τ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op (k y x) (k y x))
       have i₂ := eq65737
       grind)
    | exact superpose eq65737 eq10
    | exact resolve eq10 eq65737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65737
  have eq66039 : (M.op x x) = (M.op (k y x) (k y x)) := by
    first
    | (have i₁ := eq65978
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq65978
    | exact resolve eq65978 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65978
  have eq66427 : (k (k y x) x) = (M.op x (k y x)) := by
    first
    | (have j0 := eq11 (k y x) x
       grind)
    | (have r₁ := eq11 x (k y x)
       have r₂ := eq66039
       grind)
    | (have r₁ := eq11 (k y x) x
       have r₂ := eq66039
       grind)
    | exact resolve eq11 eq66039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66482 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (σ (k (k y x) (τ X0))) = (M.op X0 (σ (k y x))) := by
    intro X0
    first
    | (have i₁ := eq130 (k y x) X0
       have i₂ := eq66039
       grind)
    | exact superpose eq66039 eq130
    | (have j0 := eq130 x X0
       grind)
    | exact resolve eq130 eq66039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66039
  have eq66915 : x = (k y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq66427
       have i₂ := eq8775
       grind)
    | exact superpose eq8775 eq66427
    | exact resolve eq66427 eq8775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8775
  have eq67249 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq58390
       have i₂ := eq66915
       grind)
    | exact superpose eq66915 eq58390
    | exact resolve eq58390 eq66915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58390
  have eq67253 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq66915
  have eq67255 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq67249
       have r₂ := eq67253
       grind)
    | exact resolve eq67249 eq67253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67249 eq67253
  have eq73499 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq67255
       grind)
    | exact superpose eq67255 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq67255
       grind)
    | exact resolve eq13 eq67255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67255
  have eq73506 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq73499
  have eq73507 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq73506
  have eq73522 : (σ y) = (σ (k y (τ (σ x)))) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq73507
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq73507
    | exact resolve eq73507 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq73507
  have eq73531 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq73522
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq73522
    | exact resolve eq73522 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73522
  have eq73537 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq73531
       have i₂ := eq116 x
       grind)
    | exact superpose eq116 eq73531
    | exact resolve eq73531 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73531
  have eq73542 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq73537
       have i₂ := eq116 y
       grind)
    | exact superpose eq116 eq73537
    | exact resolve eq73537 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73537
  have eq81640 : (M.op (σ x) (σ (k y x))) = (σ (k (k y x) (τ (σ x)))) := by
    first
    | (have j0 := eq66482 (σ x)
       grind)
    | (have r₁ := eq66482 (σ x)
       have r₂ := eq116 x
       grind)
    | exact resolve eq66482 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66482
  have eq81666 : (M.op (σ x) (σ (k y x))) = (σ (k (k y x) x)) := by
    first
    | (have i₁ := eq81640
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq81640
    | exact resolve eq81640 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81640
  have eq81667 : (σ (M.op x (k y x))) = (M.op (σ x) (σ (k y x))) := by
    first
    | (have i₁ := eq81666
       have i₂ := eq66427
       grind)
    | exact superpose eq66427 eq81666
    | exact resolve eq81666 eq66427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66427 eq81666
  have eq81753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81667
       have i₂ := eq6967 x y
       grind)
    | exact superpose eq6967 eq81667
    | (have j1 := eq6967 x y
       grind)
    | exact resolve eq81667 eq6967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6967
  have eq81756 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq81667
       have i₂ := eq13640 y x
       grind)
    | exact superpose eq13640 eq81667
    | (have j1 := eq13640 y x
       grind)
    | exact resolve eq81667 eq13640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13640 eq81667
  have eq81820 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq81756
  have eq81821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq81753
  have eq81859 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq81820
       have r₂ := eq16
       grind)
    | exact resolve eq81820 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81820
  have eq81861 : x = (k y x) := by
    first
    | (have r₁ := eq81821
       have r₂ := eq16
       grind)
    | exact resolve eq81821 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81821
  have eq81903 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq2308
       have i₂ := eq81859
       grind)
    | exact superpose eq81859 eq2308
    | exact resolve eq2308 eq81859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308
  have eq81937 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15660
       have i₂ := eq81859
       grind)
    | exact superpose eq81859 eq15660
    | exact resolve eq15660 eq81859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15660
  have eq82419 : (σ x) = (σ y) ∨ y = (k y x) ∨ x = y ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59070
       have i₂ := eq81859
       grind)
    | exact superpose eq81859 eq59070
    | exact resolve eq59070 eq81859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59070
  have eq82659 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq73542
       have i₂ := eq81859
       grind)
    | exact superpose eq81859 eq73542
    | exact resolve eq73542 eq81859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73542 eq81859
  have eq82738 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq82659
  have eq82746 : (σ x) = (σ y) ∨ y = (k y x) ∨ x = y ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq82419
  have eq84350 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq82738
       have i₂ := eq81861
       grind)
    | exact superpose eq81861 eq82738
    | exact resolve eq82738 eq81861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82738
  have eq84473 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq82746
       have i₂ := eq81861
       grind)
    | exact superpose eq81861 eq82746
    | exact resolve eq82746 eq81861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82746
  have eq84474 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq84473
  have eq84896 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81903
       have i₂ := eq81861
       grind)
    | exact superpose eq81861 eq81903
    | exact resolve eq81903 eq81861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81903
  have eq86095 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq84896
       have r₂ := eq81937
       grind)
    | exact resolve eq84896 eq81937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81937 eq84896
  have eq86438 : (M.op y y) ≠ (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq81861
       grind)
    | exact superpose eq81861 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq81861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86561 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq86609 : x = y ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq84474
       have r₂ := eq86561
       grind)
    | exact resolve eq84474 eq86561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84474
  have eq87896 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86609
       grind)
    | exact superpose eq86609 eq16
    | exact resolve eq16 eq86609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86609
  have eq87957 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have r₁ := eq87896
       have r₂ := eq116 x
       grind)
    | exact resolve eq87896 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87896
  have eq87974 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq87957
       grind)
    | exact superpose eq87957 eq16
    | exact resolve eq16 eq87957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87957
  have eq88474 : (σ x) ≠ (σ y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq87974
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq87974
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq87974 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq88475 : (σ x) ≠ (σ x) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq87974
       have i₂ := eq17 y x
       grind)
    | exact superpose eq17 eq87974
    | (have j1 := eq17 y x
       grind)
    | exact resolve eq87974 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq88491 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq88475
  have eq88493 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq11 y x
       grind)
    | (have r₁ := eq88491
       have r₂ := eq11 y x
       grind)
    | (have r₁ := eq88491
       have r₂ := eq11 x y
       grind)
    | exact resolve eq88491 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88491
  have eq88494 : (σ x) ≠ (σ y) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have j1 := eq11 y x
       grind)
    | (have r₁ := eq88474
       have r₂ := eq11 y x
       grind)
    | (have r₁ := eq88474
       have r₂ := eq11 x y
       grind)
    | exact resolve eq88474 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88474
  have eq88495 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88493
       have i₂ := eq81861
       grind)
    | exact superpose eq81861 eq88493
    | exact resolve eq88493 eq81861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88493
  have eq88496 : x = (M.op x y) ∨ (σ x) ≠ (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq88494
       have i₂ := eq81861
       grind)
    | exact superpose eq81861 eq88494
    | exact resolve eq88494 eq81861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88494
  have eq88497 : x = y ∨ x = (M.op x y) ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq88496
       have i₂ := eq81861
       grind)
    | exact superpose eq81861 eq88496
    | exact resolve eq88496 eq81861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88496
  have eq88584 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq88495
  have eq88594 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq88497
       have r₂ := eq88584
       grind)
    | exact resolve eq88497 eq88584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88497 eq88584
  have eq88598 : x = (M.op x y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq84350
       have r₂ := eq88594
       grind)
    | exact resolve eq84350 eq88594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84350 eq88594
  have eq88762 : (σ x) ≠ (σ x) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq87974
       have i₂ := eq88598
       grind)
    | exact superpose eq88598 eq87974
    | exact resolve eq87974 eq88598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87974 eq88598
  have eq88815 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq88762
  have eq89002 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq88815
       grind)
    | exact superpose eq88815 eq9
    | exact resolve eq9 eq88815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88815
  have eq89153 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq89002
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq89002
    | exact resolve eq89002 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89002
  have eq89154 : (M.op y y) = (M.op x x) := by grind
  clear eq89153
  have eq89249 : x = (M.op x y) := by
    first
    | (have r₁ := eq86438
       have r₂ := eq89154
       grind)
    | exact resolve eq86438 eq89154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86438
  have eq89290 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89249
       grind)
    | exact superpose eq89249 eq16
    | exact resolve eq16 eq89249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89249
  have eq89433 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq86095
       have r₂ := eq89290
       grind)
    | exact resolve eq86095 eq89290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86095
  have eq89434 : (σ x) ≠ (σ y) := by
    first
    | (have r₁ := eq86561
       have r₂ := eq89290
       grind)
    | exact resolve eq86561 eq89290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86561 eq89290
  have eq90178 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (σ (k y (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq130 y X0
       have i₂ := eq89154
       grind)
    | exact superpose eq89154 eq130
    | (have j0 := eq130 x X0
       grind)
    | exact resolve eq130 eq89154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq89154
  have eq93281 : (M.op (σ x) (σ y)) = (σ (k y (τ (σ x)))) := by
    first
    | (have j0 := eq90178 (σ x)
       grind)
    | (have r₁ := eq90178 (σ x)
       have r₂ := eq116 x
       grind)
    | exact resolve eq90178 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq90178
  have eq93324 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq93281
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq93281
    | exact resolve eq93281 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93281
  have eq93327 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq93324
       have i₂ := eq81861
       grind)
    | exact superpose eq81861 eq93324
    | exact resolve eq93324 eq81861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81861 eq93324
  have eq93328 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq89433
       have i₂ := eq93327
       grind)
    | exact superpose eq93327 eq89433
    | exact resolve eq89433 eq93327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89433 eq93327
  have eq93329 : False := by grind
  exact eq93329

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else if m(Y,X) = m(Y,Y) then Y
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyy_pyx_y_pyx_pyy_pyx_pyy_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq14 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq11 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq27 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq11
    | (have j0 := eq11 X1 (σ X0)
       grind)
    | exact resolve eq11 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) ≠ (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (τ X0) X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 X1 (τ X0)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17 (σ y) (σ x)
       grind)
    | exact superpose eq17 eq16
    | (have j1 := eq17 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq17 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq17 X0 X1
       grind)
    | exact resolve eq12 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq38 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq40 : (M.op (σ x) (σ y)) = (σ (k y (τ (σ x)))) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq35
    | exact resolve eq35 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq41 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq40
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq40
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) := by
    intro X0
    first
    | (have j0 := eq27 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq44
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq49 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq39
    | (have j0 := eq39 X1 (σ X0)
       grind)
    | exact resolve eq39 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k X0 (σ X1))) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (τ X0)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq39
    | (have j0 := eq39 X1 (τ X0)
       grind)
    | exact resolve eq39 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) ≠ (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (σ (τ (k X0 (σ (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq22 X0 (τ X0)
       grind)
    | exact superpose eq22 eq45
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq56 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq66 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq10 (k X0 (σ (τ X0)))
       grind)
    | exact superpose eq10 eq58
    | exact resolve eq58 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq68 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq41
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq41
    | exact resolve eq41 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq70 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq27
    | (have j0 := eq27 X0 X1
       grind)
    | exact resolve eq27 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66
    | exact resolve eq66 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq80 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq17 y x
       grind)
    | exact superpose eq17 eq68
    | (have j1 := eq17 y x
       grind)
    | exact resolve eq68 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq80
  have eq85 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq22 X0 (τ X0)
       have i₂ := eq73 (τ X0)
       grind)
    | exact superpose eq73 eq22
    | exact resolve eq22 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq90 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq86
    | exact resolve eq86 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq94 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (M.op X0 X0)) ∨ (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | exact resolve eq32 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq98 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 (τ (σ X0)))) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X1 (σ X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq70
    | (have j0 := eq70 X1 (σ X0)
       grind)
    | (have r₁ := eq70 X0 (σ X0)
       have r₂ := eq62 X0
       grind)
    | exact resolve eq70 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq99 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq98
    | (have j0 := eq98 X0 X1
       grind)
    | exact resolve eq98 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq106 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq49
    | (have j0 := eq49 X1 (σ X0)
       grind)
    | exact resolve eq49 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op X1 (σ (σ X0))) = (σ (σ (k X0 (τ (τ X1))))) ∨ (M.op X1 X1) = (M.op X1 (σ (σ X0))) ∨ (M.op X1 X1) = (σ (σ (k X0 (τ (τ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X1) X1
       have i₂ := eq19 (τ X1) X1
       grind)
    | exact superpose eq19 eq49
    | (have j0 := eq49 (σ X0) X1
       grind)
    | exact resolve eq49 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 (τ X0))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq9
    | (have j1 := eq49 X1 X0
       grind)
    | exact resolve eq9 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq120 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq106
    | (have j0 := eq106 X0 X1
       grind)
    | exact resolve eq106 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq123 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq120
    | (have j0 := eq120 X0 X1
       grind)
    | exact resolve eq120 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq140 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (τ (M.op X1 X1)) ∨ (τ (k X1 (σ (σ X0)))) = (M.op (σ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X1 (σ X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq94
    | (have j0 := eq94 X1 (σ X0)
       grind)
    | exact resolve eq94 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X1 X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50
    | (have j0 := eq50 X1 (τ X0)
       grind)
    | exact resolve eq50 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (M.op X1 (τ (τ X0))) = (τ (τ (k X0 (σ (σ X1))))) ∨ (M.op X1 X1) = (M.op X1 (τ (τ X0))) ∨ (M.op X1 X1) = (τ (τ (k X0 (σ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (τ X0) X1
       have i₂ := eq22 X0 (σ X1)
       grind)
    | exact superpose eq22 eq50
    | (have j0 := eq50 (τ X0) X1
       grind)
    | exact resolve eq50 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (σ X0))
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq10
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq10 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq169 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X1 X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq153 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq153
    | (have j0 := eq153 X0 X1
       grind)
    | exact resolve eq153 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq172 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) ∨ (τ (M.op X0 X0)) = (τ (k X1 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq169
    | (have j0 := eq169 X0 X1
       grind)
    | exact resolve eq169 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq180 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (σ (τ (M.op X0 X0))) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X1 (τ X0)
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq101
    | (have j0 := eq101 X1 (τ X0)
       grind)
    | exact resolve eq101 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq180 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq180
    | (have j0 := eq180 X0 X1
       grind)
    | exact resolve eq180 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq186 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq183
    | (have j0 := eq183 X0 X1
       grind)
    | exact resolve eq183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq188 : ∀ X0 X1 : G, (σ (τ (k X0 (σ X1)))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq186
    | (have j0 := eq186 X0 X1
       grind)
    | exact resolve eq186 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq189 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq10 (k X0 (σ X1))
       grind)
    | exact superpose eq10 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq190 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq114 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq114
    | (have j0 := eq114 (σ X0) X1
       grind)
    | exact resolve eq114 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X1 (σ (σ X0))) = (σ (σ (k X0 (τ (τ X1))))) ∨ (M.op X1 X1) = (M.op X1 (σ (σ X0))) ∨ (τ (M.op X1 X1)) = (σ (k X0 (τ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 (σ X1)
       have i₂ := eq19 (τ X0) X1
       grind)
    | exact superpose eq19 eq114
    | (have j0 := eq114 X1 (σ X0)
       grind)
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (τ (k X0 (σ (τ X1)))) = (τ (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op X1 (σ (τ X0))) ∨ (σ (τ (k X0 (σ (τ X1))))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 (τ X0)
       have i₂ := eq22 X0 (τ X0)
       grind)
    | exact superpose eq22 eq114
    | (have j0 := eq114 X1 (τ X0)
       grind)
    | exact resolve eq114 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (τ (k X0 X1)) ∨ (M.op X1 X1) = (M.op X1 (σ (τ X0))) ∨ (σ (τ (k X0 (σ (τ X1))))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq196 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq196
    | (have j0 := eq196 X0 X1
       grind)
    | exact resolve eq196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq211 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq190 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq190
    | (have j0 := eq190 X0 X1
       grind)
    | exact resolve eq190 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq213 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (τ (M.op X1 X1)) = (τ (k X0 X1)) ∨ (σ (τ (k X0 (σ (τ X1))))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq207
    | (have j0 := eq207 X0 X1
       grind)
    | exact resolve eq207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq215 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq211 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq211
    | (have j0 := eq211 X0 X1
       grind)
    | exact resolve eq211 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq217 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 (σ (τ X1))))) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (τ (M.op X1 X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq213 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq213
    | (have j0 := eq213 X0 X1
       grind)
    | exact resolve eq213 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq218 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq215
    | (have j0 := eq215 X0 X1
       grind)
    | exact resolve eq215 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq220 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (τ (M.op X1 X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 X1
       have i₂ := eq10 (k X0 (σ (τ X1)))
       grind)
    | exact superpose eq10 eq217
    | (have j0 := eq217 X0 X1
       grind)
    | exact resolve eq217 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq222 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (τ (k X0 X1)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq220 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq220
    | (have j0 := eq220 X0 X1
       grind)
    | exact resolve eq220 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq237 : ∀ X0 X1 : G, (σ (τ (k X0 (σ X1)))) = (M.op (σ X1) (σ (τ X0))) ∨ (σ (τ (k X0 (σ X1)))) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X1 (τ X0)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq123
    | (have j0 := eq123 X1 (τ X0)
       grind)
    | exact resolve eq123 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (σ (τ (k X0 (σ X1)))) = (M.op (σ X1) X0) ∨ (σ (τ (k X0 (σ X1)))) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq237 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq237
    | (have j0 := eq237 X0 X1
       grind)
    | exact resolve eq237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq258 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (τ (k X0 (σ X1)))) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 X1
       have i₂ := eq10 (k X0 (σ X1))
       grind)
    | exact superpose eq10 eq254
    | (have j0 := eq254 X0 X1
       grind)
    | exact resolve eq254 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq260 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq258 X0 X1
       have i₂ := eq10 (k X0 (σ X1))
       grind)
    | exact superpose eq10 eq258
    | (have j0 := eq258 X0 X1
       grind)
    | exact resolve eq258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq262 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq260 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq260
    | (have j0 := eq260 X0 X1
       grind)
    | exact resolve eq260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq338 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (k X1 (τ (τ X0))))) ∨ (M.op X0 X0) = (M.op X0 (σ (σ X1))) ∨ (σ (k X1 (τ (τ X0)))) = (τ (M.op X0 (σ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ (k X1 (τ (τ X0))))
       have i₂ := eq109 X1 X0
       grind)
    | exact superpose eq109 eq9
    | (have j1 := eq109 X1 X0
       grind)
    | exact resolve eq9 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq449 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (τ (τ (k X0 (σ X1)))) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq222 (τ X0) X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq222
    | (have j0 := eq222 (τ X0) X1
       grind)
    | exact resolve eq222 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq163 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq163
    | (have j0 := eq163 (τ X0) X1
       grind)
    | exact resolve eq163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq566 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq533 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq533
    | (have j0 := eq533 X0 X1
       grind)
    | exact resolve eq533 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq574 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq566 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq566
    | (have j0 := eq566 X0 X1
       grind)
    | exact resolve eq566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq580 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq574 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq574
    | (have j0 := eq574 X0 X1
       grind)
    | exact resolve eq574 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq598 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq218 X0 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq218
    | (have j0 := eq218 X0 X1
       have j1 := eq39 X0 X1
       grind)
    | exact resolve eq218 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq218 x y
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq218
    | (have j0 := eq218 x y
       grind)
    | exact resolve eq218 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq604
  have eq616 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq598 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq623 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq615
       have r₂ := eq16
       grind)
    | exact resolve eq615 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq657 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X1) (τ X0)) ∨ (σ (M.op X1 X1)) = (τ (k X0 (σ (σ X1)))) ∨ (τ (k X0 (σ (σ X1)))) = (M.op (σ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq262 (τ X0) X1
       have i₂ := eq22 X0 (σ X1)
       grind)
    | exact superpose eq22 eq262
    | (have j0 := eq262 (τ X0) X1
       grind)
    | exact resolve eq262 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq707 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (τ (M.op X0 X0)) = (τ (k X1 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq172 X0 X1
       grind)
    | exact superpose eq172 eq10
    | (have j1 := eq172 X0 X1
       grind)
    | exact resolve eq10 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq1055 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (τ (k X1 (σ (σ X0))))) ∨ (M.op X0 X0) = (M.op X0 (τ (τ X1))) ∨ (τ (k X1 (σ (σ X0)))) = (σ (M.op X0 (τ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ (k X1 (σ (σ X0))))
       have i₂ := eq158 X1 X0
       grind)
    | exact superpose eq158 eq10
    | (have j1 := eq158 X1 X0
       grind)
    | exact resolve eq10 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq1173 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (σ (k X1 (τ (τ X0)))) ∨ (M.op X0 X0) = (M.op X0 (σ (σ X1))) ∨ (σ (k X1 (τ (τ X0)))) = (τ (M.op X0 (σ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ (k X1 (τ (τ X0))))
       have i₂ := eq195 X1 X0
       grind)
    | exact superpose eq195 eq9
    | (have j1 := eq195 X1 X0
       grind)
    | exact resolve eq9 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq1300 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (τ (k X0 (σ (τ (τ X1))))))) ∨ (M.op X1 X1) = (M.op X1 (σ (σ (τ X0)))) ∨ (σ (τ (k X0 (σ (τ (τ X1)))))) = (τ (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq338 X0 (τ X0)
       have i₂ := eq22 X0 (τ (τ X0))
       grind)
    | exact superpose eq22 eq338
    | (have j0 := eq338 X1 (τ X0)
       grind)
    | exact resolve eq338 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq1335 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 (σ (τ (τ X1))))) ∨ (M.op X1 X1) = (M.op X1 (σ (σ (τ X0)))) ∨ (σ (τ (k X0 (σ (τ (τ X1)))))) = (τ (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1300 X0 X1
       have i₂ := eq10 (k X0 (σ (τ (τ X1))))
       grind)
    | exact superpose eq10 eq1300
    | (have j0 := eq1300 X0 X1
       grind)
    | exact resolve eq1300 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq1354 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (M.op X1 X1) = (M.op X1 (σ (σ (τ X0)))) ∨ (σ (τ (k X0 (σ (τ (τ X1)))))) = (τ (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1335 X0 X1
       have i₂ := eq10 (τ X1)
       grind)
    | exact superpose eq10 eq1335
    | (have j0 := eq1335 X0 X1
       grind)
    | exact resolve eq1335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq1369 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (σ (τ (k X0 (σ (τ (τ X1)))))) = (τ (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1354 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1354
    | (have j0 := eq1354 X0 X1
       grind)
    | exact resolve eq1354 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq1376 : ∀ X0 X1 : G, (τ (M.op X1 (σ X0))) = (σ (τ (k X0 (σ (τ (τ X1)))))) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1369 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1369
    | (have j0 := eq1369 X0 X1
       grind)
    | exact resolve eq1369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1382 : ∀ X0 X1 : G, (τ (M.op X1 (σ X0))) = (k X0 (σ (τ (τ X1)))) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1376 X0 X1
       have i₂ := eq10 (k X0 (σ (τ (τ X1))))
       grind)
    | exact superpose eq10 eq1376
    | (have j0 := eq1376 X0 X1
       grind)
    | exact resolve eq1376 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq1387 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1382 X0 X1
       have i₂ := eq10 (τ X1)
       grind)
    | exact superpose eq10 eq1382
    | (have j0 := eq1382 X0 X1
       grind)
    | exact resolve eq1382 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq2760 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X0) = (k X1 X0) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq580 X0 X1
       grind)
    | exact superpose eq580 eq10
    | (have j1 := eq580 X0 X1
       grind)
    | exact resolve eq10 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3006 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq623
       grind)
    | exact superpose eq623 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq623
       grind)
    | exact resolve eq13 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq3010 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq3006
       have r₂ := eq62 x
       grind)
    | exact resolve eq3006 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3006
  have eq3014 : (σ x) = (σ (k y (τ (σ x)))) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq3010
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq3010
    | exact resolve eq3010 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3010
  have eq3017 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq3014
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq3014
    | exact resolve eq3014 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3014
  have eq3020 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq3017
       have i₂ := eq62 y
       grind)
    | exact superpose eq62 eq3017
    | exact resolve eq3017 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017
  have eq3023 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq3020
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq3020
    | exact resolve eq3020 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3020
  have eq3025 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j1 := eq101 x y
       grind)
    | (have r₁ := eq3023
       have r₂ := eq101 x y
       grind)
    | (have r₁ := eq3023
       have r₂ := eq101 y x
       grind)
    | exact resolve eq3023 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3023
  have eq3974 : ∀ X0 X1 : G, (τ (k X0 (σ (τ X1)))) = (τ (M.op X1 (σ (τ X0)))) ∨ (M.op X1 X1) = (M.op X1 (σ (τ X0))) ∨ (M.op X1 X1) = (σ (τ (k X0 (σ (τ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1387 (τ X0) X1
       have i₂ := eq22 X0 (τ X1)
       grind)
    | exact superpose eq22 eq1387
    | (have j0 := eq1387 (τ X0) X1
       grind)
    | exact resolve eq1387 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq4043 : ∀ X0 X1 : G, (τ (k X0 (σ (τ X1)))) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 (σ (τ X0))) ∨ (M.op X1 X1) = (σ (τ (k X0 (σ (τ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3974 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3974
    | (have j0 := eq3974 X0 X1
       grind)
    | exact resolve eq3974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3974
  have eq4070 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 (σ (τ X0))) ∨ (M.op X1 X1) = (σ (τ (k X0 (σ (τ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq4043 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4043
    | (have j0 := eq4043 X0 X1
       grind)
    | exact resolve eq4043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4043
  have eq4094 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (σ (τ (k X0 (σ (τ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq4070 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4070
    | (have j0 := eq4070 X0 X1
       grind)
    | exact resolve eq4070 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4070
  have eq4109 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4094 X0 X1
       have i₂ := eq10 (k X0 (σ (τ X1)))
       grind)
    | exact superpose eq10 eq4094
    | (have j0 := eq4094 X0 X1
       grind)
    | exact resolve eq4094 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4094
  have eq4117 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4109 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4109
    | (have j0 := eq4109 X0 X1
       grind)
    | exact resolve eq4109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4109
  have eq4293 : ∀ X0 X1 : G, (τ (τ (k X0 (σ X1)))) = (τ (M.op X1 (τ X0))) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4117 (τ X0) X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq4117
    | (have j0 := eq4117 (τ X0) X1
       grind)
    | exact resolve eq4117 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4117
  have eq4451 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op (τ X1) (τ (σ X0)))) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2760 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq2760
    | (have j0 := eq2760 X1 (σ X0)
       grind)
    | exact resolve eq2760 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2760
  have eq4558 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4451 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq4451
    | (have j0 := eq4451 X0 X1
       grind)
    | exact resolve eq4451 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4451
  have eq4593 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4558 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq4558
    | (have j0 := eq4558 X0 X1
       grind)
    | exact resolve eq4558 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4558
  have eq7218 : ∀ X0 X1 : G, (τ (M.op (τ X0) (τ X0))) = (τ (τ (k X1 X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq449 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq449
    | (have j0 := eq449 X1 (τ X0)
       grind)
    | exact resolve eq449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq7349 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (τ (τ (k X1 X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7218 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq7218
    | (have j0 := eq7218 X0 X1
       grind)
    | exact resolve eq7218 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7218
  have eq7401 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) ∨ (τ (τ (M.op X0 X0))) = (τ (τ (k X1 X0))) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7349 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq7349
    | (have j0 := eq7349 X0 X1
       grind)
    | exact resolve eq7349 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7349
  have eq7771 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op (τ X1) (τ (σ X0)))) ∨ (τ (M.op X1 X1)) = (τ (σ (k X0 (τ X1)))) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq707 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq707
    | (have j0 := eq707 X1 (σ X0)
       grind)
    | exact resolve eq707 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq7898 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) ∨ (τ (M.op X1 X1)) = (τ (σ (k X0 (τ X1)))) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7771 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq7771
    | (have j0 := eq7771 X0 X1
       grind)
    | exact resolve eq7771 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7771
  have eq7943 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7898 X0 X1
       have i₂ := eq9 (k X0 (τ X1))
       grind)
    | exact superpose eq9 eq7898
    | (have j0 := eq7898 X0 X1
       grind)
    | exact resolve eq7898 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7898
  have eq7968 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) X0) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7943 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq7943
    | (have j0 := eq7943 X0 X1
       grind)
    | exact resolve eq7943 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7943
  have eq10861 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (τ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (τ X1) (τ X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (τ (k X1 (σ (σ X0)))) ∨ (τ (k X1 (σ (σ X0)))) = (M.op (σ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99 X1 (τ X0)
       have i₂ := eq657 X0 X1
       grind)
    | exact superpose eq657 eq99
    | (have j0 := eq99 X0 (τ X1)
       have j1 := eq657 X1 X0
       grind)
    | (have r₁ := eq99 X1 (τ X0)
       have r₂ := eq657 X0 X1
       grind)
    | exact resolve eq99 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10867 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (τ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (τ X1) (τ X1)) ∨ (σ (M.op X0 X0)) = (τ (k X1 (σ (σ X0)))) ∨ (τ (k X1 (σ (σ X0)))) = (M.op (σ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) (σ X0)
       have i₂ := eq657 X1 X0
       grind)
    | exact superpose eq657 eq12
    | (have j0 := eq12 (τ X1) (σ X0)
       have j1 := eq657 X1 X0
       grind)
    | exact resolve eq12 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq10868 : ∀ X0 X1 : G, (σ X0) = (k (τ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (τ X1) (τ X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (τ (k X1 (σ (σ X0)))) ∨ (τ (k X1 (σ (σ X0)))) = (M.op (σ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10861 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10861
  have eq10869 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (τ (k X1 (σ (σ X0)))) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (τ X1) (τ X1)) ∨ (σ (M.op X0 X0)) = (τ (k X1 (σ (σ X0)))) ∨ (τ (k X1 (σ (σ X0)))) = (M.op (σ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10867 X0 X1
       have i₂ := eq22 X1 (σ X0)
       grind)
    | exact superpose eq22 eq10867
    | (have j0 := eq10867 X0 X1
       grind)
    | exact resolve eq10867 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10867
  have eq10871 : ∀ X0 X1 : G, (σ X0) = (τ (k X1 (σ (σ X0)))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (τ X1) (τ X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (τ (k X1 (σ (σ X0)))) ∨ (τ (k X1 (σ (σ X0)))) = (M.op (σ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10868 X0 X1
       have i₂ := eq22 X1 (σ X0)
       grind)
    | exact superpose eq22 eq10868
    | (have j0 := eq10868 X0 X1
       grind)
    | exact resolve eq10868 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10868
  have eq10887 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (τ (k X1 (σ (σ X0)))) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (τ X1) (τ X1)) ∨ (σ (M.op X0 X0)) = (τ (k X1 (σ (σ X0)))) ∨ (τ (k X1 (σ (σ X0)))) = (M.op (σ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10869 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq10869
    | (have j0 := eq10869 X0 X1
       grind)
    | exact resolve eq10869 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10869
  have eq10888 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (τ (k X1 (σ (σ X0)))) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (τ X1) (τ X1)) ∨ (τ (k X1 (σ (σ X0)))) = (M.op (σ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10887 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10887
  have eq10890 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (τ (M.op X1 X1)) ∨ (σ X0) = (τ (k X1 (σ (σ X0)))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (τ (k X1 (σ (σ X0)))) ∨ (τ (k X1 (σ (σ X0)))) = (M.op (σ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10871 X0 X1
       have i₂ := eq90 X1
       grind)
    | exact superpose eq90 eq10871
    | (have j0 := eq10871 X0 X1
       grind)
    | exact resolve eq10871 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10871
  have eq10906 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (τ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (τ (k X1 (σ (σ X0)))) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (τ (k X1 (σ (σ X0)))) = (M.op (σ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10888 X0 X1
       have i₂ := eq90 X1
       grind)
    | exact superpose eq90 eq10888
    | (have j0 := eq10888 X0 X1
       grind)
    | exact resolve eq10888 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10888
  have eq10908 : ∀ X0 X1 : G, (σ X0) = (τ (k X1 (σ (σ X0)))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (τ (k X1 (σ (σ X0)))) ∨ (τ (k X1 (σ (σ X0)))) = (M.op (σ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10890 X0 X1
       have j1 := eq140 X0 X1
       grind)
    | (have r₁ := eq10890 X0 X1
       have r₂ := eq140 X0 X1
       grind)
    | exact resolve eq10890 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq10890
  have eq10913 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (τ (k X1 (σ (σ X0)))) ∨ (τ (k X1 (σ (σ X0)))) = (M.op (σ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10906 X0 X1
       have j1 := eq94 X1 (σ X0)
       grind)
    | (have r₁ := eq10906 X0 X0
       have r₂ := eq94 X0 (σ X0)
       grind)
    | exact resolve eq10906 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq10906
  have eq10918 : ∀ X0 X1 : G, (τ (k X1 (σ (σ X0)))) = (M.op (σ X0) (τ X1)) ∨ (σ (M.op X0 X0)) = (τ (k X1 (σ (σ X0)))) ∨ (σ X0) = (τ (k X1 (σ (σ X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq10908 X0 X1
       have j1 := eq10913 X0 X1
       grind)
    | (have r₁ := eq10908 X0 X1
       have r₂ := eq10913 X0 X1
       grind)
    | exact resolve eq10908 eq10913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10908 eq10913
  have eq11000 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (σ (k X0 (τ (σ (σ X1))))))) ∨ (M.op X1 X1) = (M.op X1 (τ (τ (σ X0)))) ∨ (τ (σ (k X0 (τ (σ (σ X1)))))) = (σ (M.op X1 (τ (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1055 X0 (σ X1)
       have i₂ := eq19 (σ (σ X0)) X1
       grind)
    | exact superpose eq19 eq1055
    | (have j0 := eq1055 X1 (σ X0)
       grind)
    | exact resolve eq1055 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq11120 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k X0 (τ (σ (σ X1))))) ∨ (M.op X1 X1) = (M.op X1 (τ (τ (σ X0)))) ∨ (τ (σ (k X0 (τ (σ (σ X1)))))) = (σ (M.op X1 (τ (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq11000 X0 X1
       have i₂ := eq9 (k X0 (τ (σ (σ X1))))
       grind)
    | exact superpose eq9 eq11000
    | (have j0 := eq11000 X0 X1
       grind)
    | exact resolve eq11000 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11000
  have eq11194 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k X0 (σ X1))) ∨ (M.op X1 X1) = (M.op X1 (τ (τ (σ X0)))) ∨ (τ (σ (k X0 (τ (σ (σ X1)))))) = (σ (M.op X1 (τ (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq11120 X0 X1
       have i₂ := eq9 (σ X1)
       grind)
    | exact superpose eq9 eq11120
    | (have j0 := eq11120 X0 X1
       grind)
    | exact resolve eq11120 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11120
  have eq11254 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (τ (k X0 (σ X1))) ∨ (τ (σ (k X0 (τ (σ (σ X1)))))) = (σ (M.op X1 (τ (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq11194 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11194
    | (have j0 := eq11194 X0 X1
       grind)
    | exact resolve eq11194 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11194
  have eq11283 : ∀ X0 X1 : G, (τ (σ (k X0 (τ (σ (σ X1)))))) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11254 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11254
    | (have j0 := eq11254 X0 X1
       grind)
    | exact resolve eq11254 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11254
  have eq11299 : ∀ X0 X1 : G, (k X0 (τ (σ (σ X1)))) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11283 X0 X1
       have i₂ := eq9 (k X0 (τ (σ (σ X1))))
       grind)
    | exact superpose eq9 eq11283
    | (have j0 := eq11283 X0 X1
       grind)
    | exact resolve eq11283 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11283
  have eq11309 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11299 X0 X1
       have i₂ := eq9 (σ X1)
       grind)
    | exact superpose eq9 eq11299
    | (have j0 := eq11299 X0 X1
       grind)
    | exact resolve eq11299 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11299
  have eq11375 : ∀ X0 X1 : G, (σ (k X0 (τ (σ X1)))) = (σ (M.op X1 (τ (σ X0)))) ∨ (M.op X1 X1) = (M.op X1 (τ (σ X0))) ∨ (M.op X1 X1) = (τ (σ (k X0 (τ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq11309 (σ X1) X1
       have i₂ := eq19 (σ X1) X1
       grind)
    | exact superpose eq19 eq11309
    | (have j0 := eq11309 (σ X0) X1
       grind)
    | exact resolve eq11309 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11309
  have eq11466 : ∀ X0 X1 : G, (σ (k X0 (τ (σ X1)))) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 (τ (σ X0))) ∨ (M.op X1 X1) = (τ (σ (k X0 (τ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq11375 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11375
    | (have j0 := eq11375 X0 X1
       grind)
    | exact resolve eq11375 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11375
  have eq11506 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 (τ (σ X0))) ∨ (M.op X1 X1) = (τ (σ (k X0 (τ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq11466 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq11466
    | (have j0 := eq11466 X0 X1
       grind)
    | exact resolve eq11466 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11466
  have eq11539 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (σ (k X0 (τ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq11506 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11506
    | (have j0 := eq11506 X0 X1
       grind)
    | exact resolve eq11506 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11506
  have eq11553 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11539 X0 X1
       have i₂ := eq9 (k X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq11539
    | (have j0 := eq11539 X0 X1
       grind)
    | exact resolve eq11539 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11539
  have eq11558 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11553 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq11553
    | (have j0 := eq11553 X0 X1
       grind)
    | exact resolve eq11553 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11553
  have eq11601 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (σ (τ (k X0 (σ (τ (τ X1)))))) ∨ (M.op X1 X1) = (M.op X1 (σ (σ (τ X0)))) ∨ (σ (τ (k X0 (σ (τ (τ X1)))))) = (τ (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1173 X0 (τ X0)
       have i₂ := eq22 X0 (τ (τ X0))
       grind)
    | exact superpose eq22 eq1173
    | (have j0 := eq1173 X1 (τ X0)
       grind)
    | exact resolve eq1173 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq11709 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (k X0 (σ (τ (τ X1)))) ∨ (M.op X1 X1) = (M.op X1 (σ (σ (τ X0)))) ∨ (σ (τ (k X0 (σ (τ (τ X1)))))) = (τ (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq11601 X0 X1
       have i₂ := eq10 (k X0 (σ (τ (τ X1))))
       grind)
    | exact superpose eq10 eq11601
    | (have j0 := eq11601 X0 X1
       grind)
    | exact resolve eq11601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11601
  have eq11765 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op X1 (σ (σ (τ X0)))) ∨ (σ (τ (k X0 (σ (τ (τ X1)))))) = (τ (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq11709 X0 X1
       have i₂ := eq10 (τ X1)
       grind)
    | exact superpose eq10 eq11709
    | (have j0 := eq11709 X0 X1
       grind)
    | exact resolve eq11709 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11709
  have eq11802 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (k X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (σ (τ (k X0 (σ (τ (τ X1)))))) = (τ (M.op X1 (σ (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq11765 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11765
    | (have j0 := eq11765 X0 X1
       grind)
    | exact resolve eq11765 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11765
  have eq11823 : ∀ X0 X1 : G, (τ (M.op X1 (σ X0))) = (σ (τ (k X0 (σ (τ (τ X1)))))) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (k X0 (τ X1)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11802 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11802
    | (have j0 := eq11802 X0 X1
       grind)
    | exact resolve eq11802 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11802
  have eq11841 : ∀ X0 X1 : G, (τ (M.op X1 (σ X0))) = (k X0 (σ (τ (τ X1)))) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (k X0 (τ X1)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11823 X0 X1
       have i₂ := eq10 (k X0 (σ (τ (τ X1))))
       grind)
    | exact superpose eq10 eq11823
    | (have j0 := eq11823 X0 X1
       grind)
    | exact resolve eq11823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11823
  have eq11852 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (k X0 (τ X1)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11841 X0 X1
       have i₂ := eq10 (τ X1)
       grind)
    | exact superpose eq10 eq11841
    | (have j0 := eq11841 X0 X1
       grind)
    | exact resolve eq11841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11841
  have eq12086 : ∀ X0 X1 : G, (τ (k X0 (σ (τ X1)))) = (τ (M.op X1 (σ (τ X0)))) ∨ (M.op X1 X1) = (M.op X1 (σ (τ X0))) ∨ (τ (k X0 (σ (τ X1)))) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11852 (τ X0) X1
       have i₂ := eq22 X0 (τ X1)
       grind)
    | exact superpose eq22 eq11852
    | (have j0 := eq11852 (τ X0) X1
       grind)
    | exact resolve eq11852 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11852
  have eq12199 : ∀ X0 X1 : G, (τ (k X0 (σ (τ X1)))) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 (σ (τ X0))) ∨ (τ (k X0 (σ (τ X1)))) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12086 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12086
    | (have j0 := eq12086 X0 X1
       grind)
    | exact resolve eq12086 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12086
  have eq12243 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 (σ (τ X0))) ∨ (τ (k X0 (σ (τ X1)))) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12199 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq12199
    | (have j0 := eq12199 X0 X1
       grind)
    | exact resolve eq12199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12199
  have eq12284 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ (k X0 (σ (τ X1)))) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12243 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12243
    | (have j0 := eq12243 X0 X1
       grind)
    | exact resolve eq12243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12243
  have eq12306 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (τ (M.op X1 X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12284 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq12284
    | (have j0 := eq12284 X0 X1
       grind)
    | exact resolve eq12284 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12284
  have eq12413 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81
       have i₂ := eq616 x y
       grind)
    | exact superpose eq616 eq81
    | (have j1 := eq616 x y
       grind)
    | exact resolve eq81 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq616
  have eq12414 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq12413
  have eq12434 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq12414
       have r₂ := eq16
       grind)
    | exact resolve eq12414 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12414
  have eq12697 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq12434
       grind)
    | exact superpose eq12434 eq68
    | exact resolve eq68 eq12434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq12698 : (M.op x x) ≠ (M.op x x) ∨ x = (k y x) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq12434
       grind)
    | exact superpose eq12434 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq12434
       grind)
    | exact resolve eq13 eq12434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12700 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) := by grind
  clear eq12698
  have eq12701 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq12697
  have eq13134 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq99 x (σ y)
       have i₂ := eq12700
       grind)
    | exact superpose eq12700 eq99
    | (have j0 := eq99 x (σ y)
       grind)
    | (have r₁ := eq99 x (σ y)
       have r₂ := eq12700
       grind)
    | exact resolve eq99 eq12700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq12700
  have eq13141 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) := by grind
  clear eq13134
  have eq13144 : (σ x) = (σ (k y (τ (σ x)))) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13141
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq13141
    | exact resolve eq13141 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13141
  have eq13150 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13144
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq13144
    | exact resolve eq13144 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13144
  have eq13153 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13150
       have i₂ := eq62 y
       grind)
    | exact superpose eq62 eq13150
    | exact resolve eq13150 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13150
  have eq20750 : ∀ X0 X1 : G, (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4293 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4293
    | (have j0 := eq4293 X1 (τ X0)
       grind)
    | exact resolve eq4293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4293
  have eq20966 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (M.op (τ X0) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20750 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq20750
    | (have j0 := eq20750 X0 X1
       grind)
    | exact resolve eq20750 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20750
  have eq21046 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X1 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq20966 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq20966
    | (have j0 := eq20966 X0 X1
       grind)
    | exact resolve eq20966 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20966
  have eq22868 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op (τ X1) X0)) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq4593 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4593
  have eq37821 : (M.op x x) ≠ (M.op x x) ∨ x = (k y x) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3025
       grind)
    | exact superpose eq3025 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3025
       grind)
    | exact resolve eq13 eq3025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3025
  have eq37822 : x = (k y x) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq37821
  have eq38802 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (τ (τ (k X1 X0))) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq7401 X0 X1
       grind)
    | exact superpose eq7401 eq10
    | (have j1 := eq7401 X0 X1
       grind)
    | exact resolve eq10 eq7401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7401
  have eq50054 : ∀ X0 X1 : G, (τ (τ (M.op X1 X1))) = (τ (τ (σ (k X0 (τ X1))))) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) (τ (σ X0)))) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38802 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq38802
    | (have j0 := eq38802 X1 (σ X0)
       grind)
    | exact resolve eq38802 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38802
  have eq50352 : ∀ X0 X1 : G, (τ (τ (M.op X1 X1))) = (τ (k X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) (τ (σ X0)))) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq50054 X0 X1
       have i₂ := eq9 (k X0 (τ X1))
       grind)
    | exact superpose eq9 eq50054
    | (have j0 := eq50054 X0 X1
       grind)
    | exact resolve eq50054 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50054
  have eq50467 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) ∨ (τ (τ (M.op X1 X1))) = (τ (k X0 (τ X1))) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq50352 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq50352
    | (have j0 := eq50352 X0 X1
       grind)
    | exact resolve eq50352 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50352
  have eq50537 : ∀ X0 X1 : G, (τ (τ (M.op X1 X1))) = (τ (k X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50467 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq50467
    | (have j0 := eq50467 X0 X1
       grind)
    | exact resolve eq50467 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50467
  have eq54357 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 X1
       have i₂ := eq21046 X0 X1
       grind)
    | exact superpose eq21046 eq580
    | (have j0 := eq580 X0 X1
       have j1 := eq21046 X0 X1
       grind)
    | exact resolve eq580 eq21046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21046
  have eq54450 : ∀ X0 X1 : G, (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X0) = (k X1 X0) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq54357 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54357
  have eq54712 : ∀ X0 X1 : G, (τ (τ (σ (k X0 (τ X1))))) = (τ (M.op (τ X1) (τ (σ X0)))) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq54450 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq54450
    | (have j0 := eq54450 X1 (σ X0)
       grind)
    | exact resolve eq54450 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54450
  have eq55031 : ∀ X0 X1 : G, (τ (τ (σ (k X0 (τ X1))))) = (τ (M.op (τ X1) X0)) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq54712 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq54712
    | (have j0 := eq54712 X0 X1
       grind)
    | exact resolve eq54712 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54712
  have eq55145 : ∀ X0 X1 : G, (τ (k X0 (τ X1))) = (τ (M.op (τ X1) X0)) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq55031 X0 X1
       have i₂ := eq9 (k X0 (τ X1))
       grind)
    | exact superpose eq9 eq55031
    | (have j0 := eq55031 X0 X1
       grind)
    | exact resolve eq55031 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55031
  have eq55209 : ∀ X0 X1 : G, (τ (k X0 (τ X1))) = (τ (M.op (τ X1) X0)) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq55145 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq55145
    | (have j0 := eq55145 X0 X1
       grind)
    | exact resolve eq55145 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55145
  have eq56325 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55209 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq55209
    | exact resolve eq55209 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55209
  have eq56578 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (M.op X0 X0))) ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56325 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq56325
    | (have j0 := eq56325 X0 X1
       grind)
    | exact resolve eq56325 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56325
  have eq56626 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56578 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq56578
    | (have j0 := eq56578 X0 X1
       grind)
    | exact resolve eq56578 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56578
  have eq56635 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56626 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq56626
    | (have j0 := eq56626 X0 X1
       grind)
    | exact resolve eq56626 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56626
  have eq60794 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (τ (M.op (σ X0) (σ X0)))) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq50537 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq50537
    | exact resolve eq50537 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50537
  have eq61036 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (τ (σ (M.op X0 X0)))) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq60794 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq60794
    | (have j0 := eq60794 X0 X1
       grind)
    | exact resolve eq60794 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60794
  have eq61061 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X1 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61036 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq61036
    | (have j0 := eq61036 X0 X1
       grind)
    | exact resolve eq61036 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61036
  have eq61072 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (τ (k X1 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61061 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq61061
    | (have j0 := eq61061 X0 X1
       grind)
    | exact resolve eq61061 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61061
  have eq61076 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (τ (M.op X0 X0)) = (τ (k X1 X0)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq61072 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq61072
    | (have j0 := eq61072 X0 X1
       grind)
    | exact resolve eq61072 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61072
  have eq84215 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (τ (k X1 (σ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ (k X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10918 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10918
    | exact resolve eq10918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84257 : ∀ X0 X1 : G, (M.op (σ X1) (τ (σ X0))) = (τ (σ (k X0 (τ (σ (σ X1)))))) ∨ (σ (M.op X1 X1)) = (τ (σ (k X0 (τ (σ (σ X1)))))) ∨ (σ X1) = (τ (σ (k X0 (τ (σ (σ X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq10918 X0 (σ X1)
       have i₂ := eq19 (σ (σ X0)) X1
       grind)
    | exact superpose eq19 eq10918
    | exact resolve eq10918 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10918
  have eq84336 : ∀ X0 X1 : G, (k X0 (τ (σ (σ X1)))) = (M.op (σ X1) (τ (σ X0))) ∨ (σ (M.op X1 X1)) = (τ (σ (k X0 (τ (σ (σ X1)))))) ∨ (σ X1) = (τ (σ (k X0 (τ (σ (σ X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq84257 X0 X1
       have i₂ := eq9 (k X0 (τ (σ (σ X1))))
       grind)
    | exact superpose eq9 eq84257
    | (have j0 := eq84257 X0 X1
       grind)
    | exact resolve eq84257 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84257
  have eq84353 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (τ (k X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84215 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq84215
    | (have j0 := eq84215 X0 X1
       grind)
    | exact resolve eq84215 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84215
  have eq84376 : ∀ X0 X1 : G, (M.op (σ X1) X0) = (k X0 (τ (σ (σ X1)))) ∨ (σ (M.op X1 X1)) = (τ (σ (k X0 (τ (σ (σ X1)))))) ∨ (σ X1) = (τ (σ (k X0 (τ (σ (σ X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq84336 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq84336
    | (have j0 := eq84336 X0 X1
       grind)
    | exact resolve eq84336 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84336
  have eq84391 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X0 X0) = (τ (k X1 (σ X0))) ∨ (τ (k X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84353 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq84353
    | (have j0 := eq84353 X0 X1
       grind)
    | exact resolve eq84353 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84353
  have eq84412 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (τ (σ (k X0 (τ (σ (σ X1)))))) ∨ (σ X1) = (τ (σ (k X0 (τ (σ (σ X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq84376 X0 X1
       have i₂ := eq9 (σ X1)
       grind)
    | exact superpose eq9 eq84376
    | (have j0 := eq84376 X0 X1
       grind)
    | exact resolve eq84376 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84376
  have eq84441 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (k X0 (τ (σ (σ X1)))) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (τ (σ (k X0 (τ (σ (σ X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq84412 X0 X1
       have i₂ := eq9 (k X0 (τ (σ (σ X1))))
       grind)
    | exact superpose eq9 eq84412
    | (have j0 := eq84412 X0 X1
       grind)
    | exact resolve eq84412 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84412
  have eq84460 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (τ (σ (k X0 (τ (σ (σ X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq84441 X0 X1
       have i₂ := eq9 (σ X1)
       grind)
    | exact superpose eq9 eq84441
    | (have j0 := eq84441 X0 X1
       grind)
    | exact resolve eq84441 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84441
  have eq84473 : ∀ X0 X1 : G, (σ X1) = (k X0 (τ (σ (σ X1)))) ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq84460 X0 X1
       have i₂ := eq9 (k X0 (τ (σ (σ X1))))
       grind)
    | exact superpose eq9 eq84460
    | (have j0 := eq84460 X0 X1
       grind)
    | exact resolve eq84460 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84460
  have eq84478 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84473 X0 X1
       have i₂ := eq9 (σ X1)
       grind)
    | exact superpose eq9 eq84473
    | (have j0 := eq84473 X0 X1
       grind)
    | exact resolve eq84473 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84473
  have eq84889 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84478 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84478
    | exact resolve eq84478 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84931 : ∀ X0 X1 : G, (σ (k X0 (τ (σ X1)))) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 (τ (σ X1)))) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (k X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq84478 (σ X1) X1
       have i₂ := eq19 (σ X1) X1
       grind)
    | exact superpose eq19 eq84478
    | exact resolve eq84478 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84478
  have eq85060 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 (τ (σ X1)))) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (k X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq84931 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq84931
    | (have j0 := eq84931 X0 X1
       grind)
    | exact resolve eq84931 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84931
  have eq85067 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84889 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq84889
    | (have j0 := eq84889 X0 X1
       grind)
    | exact resolve eq84889 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84889
  have eq85115 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq85060 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq85060
    | (have j0 := eq85060 X0 X1
       grind)
    | exact resolve eq85060 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85060
  have eq85121 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85067 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq85067
    | (have j0 := eq85067 X0 X1
       grind)
    | exact resolve eq85067 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85067
  have eq85148 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85115 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq85115
    | (have j0 := eq85115 X0 X1
       grind)
    | exact resolve eq85115 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85115
  have eq85387 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85121 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq85121
    | exact resolve eq85121 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85559 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq85121 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85121
  have eq86055 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85559 X0 (τ X0)
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq85559
    | (have j0 := eq85559 X1 (τ X0)
       grind)
    | exact resolve eq85559 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86070 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq85559 y x
       have i₂ := eq12434
       grind)
    | exact superpose eq12434 eq85559
    | (have j0 := eq85559 y x
       grind)
    | (have r₁ := eq85559 y x
       have r₂ := eq12434
       grind)
    | exact resolve eq85559 eq12434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85559
  have eq86076 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (k y x) ∨ (k y x) = (M.op x x) := by grind
  clear eq86070
  have eq87709 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (k X1 (σ X0))) ∨ (τ (k X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (σ X0))
       have i₂ := eq84391 X0 X1
       grind)
    | exact superpose eq84391 eq10
    | (have j1 := eq84391 X0 X1
       grind)
    | exact resolve eq10 eq84391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84391
  have eq88749 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq85148 X1 X0
       grind)
    | exact superpose eq85148 eq9
    | (have j1 := eq85148 X1 X0
       grind)
    | exact resolve eq9 eq85148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88782 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq85148 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85148
  have eq89864 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op (τ X0) (τ X0)) = (τ (k X1 X0)) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87709 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87709
    | exact resolve eq87709 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87709
  have eq90136 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X1 X0)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89864 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq89864
    | (have j0 := eq89864 X0 X1
       grind)
    | exact resolve eq89864 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89864
  have eq92785 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 X0)) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k X1 (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 (τ X0))
       have i₂ := eq85387 X1 X0
       grind)
    | exact superpose eq85387 eq9
    | (have j1 := eq85387 X1 X0
       grind)
    | exact resolve eq9 eq85387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92811 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq85387 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85387
  have eq93162 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (k X1 (τ (σ X0)))) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq92811 X1 (σ X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq92811
    | (have j0 := eq92811 X1 (σ X0)
       grind)
    | exact resolve eq92811 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92811
  have eq93165 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq93162 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq93162
    | (have j0 := eq93162 X0 X1
       grind)
    | exact resolve eq93162 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93162
  have eq93166 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93165 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq93165
    | (have j0 := eq93165 X0 X1
       grind)
    | exact resolve eq93165 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93165
  have eq93169 : x = (k y x) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j1 := eq93166 x y
       grind)
    | (have r₁ := eq37822
       have r₂ := eq93166 x x
       grind)
    | exact resolve eq37822 eq93166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37822 eq93166
  have eq96432 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq88749 X0 X1
       grind)
    | exact superpose eq88749 eq9
    | (have j1 := eq88749 X0 X1
       grind)
    | exact resolve eq9 eq88749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88749
  have eq96479 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq96432 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq96432
    | (have j0 := eq96432 X0 X1
       grind)
    | exact resolve eq96432 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96432
  have eq97491 : ∀ X0 X1 : G, (σ X1) = (σ (τ (k X0 (σ X1)))) ∨ (τ (k X0 (σ X1))) = (τ (M.op (σ X1) (σ (τ X0)))) ∨ (M.op X1 X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq96479 X1 (τ X0)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq96479
    | exact resolve eq96479 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97608 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq96479 X0 X1
       grind)
    | exact superpose eq96479 eq9
    | (have j1 := eq96479 X0 X1
       grind)
    | exact resolve eq9 eq96479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96479
  have eq97681 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq97608 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq97608
    | (have j0 := eq97608 X0 X1
       grind)
    | exact resolve eq97608 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97608
  have eq97745 : ∀ X0 X1 : G, (σ X1) = (k X0 (σ X1)) ∨ (τ (k X0 (σ X1))) = (τ (M.op (σ X1) (σ (τ X0)))) ∨ (M.op X1 X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq97491 X0 X1
       have i₂ := eq10 (k X0 (σ X1))
       grind)
    | exact superpose eq10 eq97491
    | (have j0 := eq97491 X0 X1
       grind)
    | exact resolve eq97491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97491
  have eq97790 : ∀ X0 X1 : G, (σ X1) = (k X0 (σ X1)) ∨ (τ (k X0 (σ X1))) = (τ (M.op (σ X1) X0)) ∨ (M.op X1 X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq97745 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97745
    | (have j0 := eq97745 X0 X1
       grind)
    | exact resolve eq97745 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97745
  have eq98079 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (σ (k X0 (τ X1))) = (τ (M.op (σ X1) (σ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq97681 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq97681
    | exact resolve eq97681 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98080 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (τ (M.op (σ X1) (σ (τ X0)))) ∨ (τ (k X0 (σ X1))) = X1 ∨ (M.op X1 X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq97681 X1 (τ X0)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq97681
    | exact resolve eq97681 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98250 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op (σ (τ X0)) (σ X1))) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) X1) ∨ (σ (M.op (τ X0) X1)) = (σ (τ (M.op (σ (τ X0)) (σ X1)))) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7968 X1 X1
       have i₂ := eq97681 (τ X1) X1
       grind)
    | exact superpose eq97681 eq7968
    | (have j0 := eq7968 X1 X0
       have j1 := eq97681 (τ X0) X1
       grind)
    | exact resolve eq7968 eq97681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7968
  have eq98270 : ∀ X0 X1 : G, (τ (M.op (σ X1) (σ X0))) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq97681 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98271 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq97681 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97681
  have eq98296 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op X0 (σ X1))) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) X1) ∨ (σ (M.op (τ X0) X1)) = (σ (τ (M.op (σ (τ X0)) (σ X1)))) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98250 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98250
    | (have j0 := eq98250 X0 X1
       grind)
    | exact resolve eq98250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98250
  have eq98418 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k X0 (σ X1))) ∨ (τ (k X0 (σ X1))) = X1 ∨ (τ (k X0 (σ X1))) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98080 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98080
    | (have j0 := eq98080 X0 X1
       grind)
    | exact resolve eq98080 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98080
  have eq98436 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) ∨ (τ (M.op X0 X0)) = (τ (M.op X0 (σ X1))) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98296 X0 X1
       have i₂ := eq10 (M.op (σ (τ X0)) (σ X1))
       grind)
    | exact superpose eq10 eq98296
    | (have j0 := eq98296 X0 X1
       grind)
    | exact resolve eq98296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98296
  have eq98537 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = (τ (M.op X0 (σ X1))) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98436 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98436
    | (have j0 := eq98436 X0 X1
       grind)
    | exact resolve eq98436 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98436
  have eq98591 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = (τ (M.op X0 (σ X1))) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98537 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq98537
    | (have j0 := eq98537 X0 X1
       grind)
    | exact resolve eq98537 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98537
  have eq98615 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = (τ (M.op X0 (σ X1))) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq98591 X0 X1
       have j1 := eq86055 X0 X1
       grind)
    | (have r₁ := eq98591 X0 X1
       have r₂ := eq86055 X0 X1
       grind)
    | exact resolve eq98591 eq86055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98591
  have eq98957 : ∀ X0 X1 : G, (τ (M.op (σ X1) X0)) ≠ X1 ∨ (k (τ X0) X1) = X1 ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq98270 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98270
    | (have j0 := eq98270 (τ X0) X1
       grind)
    | exact resolve eq98270 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98270
  have eq99013 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = X1 ∨ (τ (M.op (σ X1) X0)) ≠ X1 ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq98957 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq98957
    | (have j0 := eq98957 X0 X1
       grind)
    | exact resolve eq98957 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98957
  have eq99045 : ∀ X0 X1 : G, (τ (M.op (σ X1) X0)) ≠ X1 ∨ (τ (k X0 (σ X1))) = X1 ∨ (M.op X1 X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq99013 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq99013
    | (have j0 := eq99013 X0 X1
       grind)
    | exact resolve eq99013 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99013
  have eq99566 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) ≠ (τ (M.op X0 (σ X1))) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98271 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98271
    | (have j0 := eq98271 X1 (τ X0)
       grind)
    | exact resolve eq98271 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99602 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (M.op (σ X1) X0)) ∨ (k (τ X0) X1) = X1 ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq98271 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98271
    | (have j0 := eq98271 (τ X0) X1
       grind)
    | exact resolve eq98271 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99645 : (M.op x x) ≠ (τ (σ (M.op x x))) ∨ x = (k y x) ∨ (k y x) = (M.op x x) ∨ x = (k y x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq98271 y x
       have i₂ := eq86076
       grind)
    | exact superpose eq86076 eq98271
    | (have j0 := eq98271 y x
       grind)
    | exact resolve eq98271 eq86076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86076 eq98271
  have eq99651 : (M.op x x) ≠ (τ (σ (M.op x x))) ∨ x = (k y x) ∨ (k y x) = (M.op x x) := by grind
  clear eq99645
  have eq99655 : x = (k y x) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq99651
       have r₂ := eq9 (M.op x x)
       grind)
    | exact resolve eq99651 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99651
  have eq99656 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = X1 ∨ (M.op X1 X1) ≠ (τ (M.op (σ X1) X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq99602 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq99602
    | (have j0 := eq99602 X0 X1
       grind)
    | exact resolve eq99602 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99602
  have eq99675 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 (σ X1))) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99566 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq99566
    | (have j0 := eq99566 X0 X1
       grind)
    | (have r₁ := eq99566 (σ X1) X1
       have r₂ := eq90 (σ X1)
       grind)
    | exact resolve eq99566 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99566
  have eq99679 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (M.op (σ X1) X0)) ∨ (τ (k X0 (σ X1))) = X1 ∨ (M.op X1 X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq99656 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq99656
    | (have j0 := eq99656 X0 X1
       grind)
    | exact resolve eq99656 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99656
  have eq99696 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 (σ X1))) ∨ (k X1 (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99675 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq99675
    | (have j0 := eq99675 X0 X1
       grind)
    | exact resolve eq99675 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99675
  have eq99701 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq98615 X0 X1
       have j1 := eq99696 X0 X1
       grind)
    | (have r₁ := eq98615 X0 X1
       have r₂ := eq99696 X0 X1
       grind)
    | (have r₁ := eq98615 (σ X1) X1
       have r₂ := eq99696 (σ X1) X1
       grind)
    | exact resolve eq98615 eq99696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98615 eq99696
  have eq100086 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq99655
       have i₂ := eq39 x y
       grind)
    | exact superpose eq39 eq99655
    | (have j1 := eq39 x y
       grind)
    | exact resolve eq99655 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq100105 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq218 x y
       have i₂ := eq99655
       grind)
    | exact superpose eq99655 eq218
    | (have j0 := eq218 x y
       grind)
    | exact resolve eq218 eq99655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq100116 : (τ x) = (M.op (τ x) (τ y)) ∨ x = (M.op x x) ∨ (τ (M.op x x)) = (M.op (τ x) (τ y)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq580 x y
       have i₂ := eq99655
       grind)
    | exact superpose eq99655 eq580
    | (have j0 := eq580 x y
       grind)
    | exact resolve eq580 eq99655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq100153 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq11558 y x
       have i₂ := eq99655
       grind)
    | exact superpose eq99655 eq11558
    | (have j0 := eq11558 y x
       grind)
    | exact resolve eq11558 eq99655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11558
  have eq100178 : x ≠ (M.op x x) ∨ (k y x) = (M.op x x) := by grind
  have eq100185 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (k y x) = (M.op x x) := by grind
  clear eq100086
  have eq100192 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq100153
       have r₂ := eq100178
       grind)
    | exact resolve eq100153 eq100178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100153
  have eq100202 : (τ x) = (M.op (τ x) (τ y)) ∨ (τ (M.op x x)) = (M.op (τ x) (τ y)) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq100116
       have r₂ := eq100178
       grind)
    | exact resolve eq100116 eq100178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100116
  have eq100203 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq100105
       have r₂ := eq100178
       grind)
    | exact resolve eq100105 eq100178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100105
  have eq101183 : x ≠ x ∨ (k y x) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq100185
       grind)
    | exact superpose eq100185 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq100185
       grind)
    | exact resolve eq12 eq100185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100185
  have eq101198 : x ≠ x ∨ (k y x) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq101183
  have eq101199 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (k y x) = (M.op x x) := by grind
  clear eq101198
  have eq104211 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X1 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99045 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99045
    | exact resolve eq99045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99045
  have eq104245 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X0)) = (τ (k X1 X0)) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq104211 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq104211
    | (have j0 := eq104211 X0 X1
       grind)
    | exact resolve eq104211 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104211
  have eq107174 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) ≠ (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X1 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99679 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99679
    | exact resolve eq99679 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99679
  have eq107202 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X1 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq107174 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq107174
    | (have j0 := eq107174 X0 X1
       grind)
    | (have r₁ := eq107174 X0 X0
       have r₂ := eq90 X0
       grind)
    | exact resolve eq107174 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107174
  have eq107208 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X0)) = (τ (k X1 X0)) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq107202 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq107202
    | (have j0 := eq107202 X0 X1
       grind)
    | exact resolve eq107202 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107202
  have eq112028 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100203
       grind)
    | exact superpose eq100203 eq16
    | exact resolve eq16 eq100203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100203
  have eq113041 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k y x) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq112028
       have i₂ := eq100192
       grind)
    | exact superpose eq100192 eq112028
    | exact resolve eq112028 eq100192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100192
  have eq113044 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k y x) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq112028
       have i₂ := eq101199
       grind)
    | exact superpose eq101199 eq112028
    | exact resolve eq112028 eq101199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112028
  have eq113050 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k y x) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq113044
  have eq113051 : (σ x) = (M.op (σ x) (σ y)) ∨ (k y x) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq113050
  have eq113056 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k y x) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq113041
  have eq113057 : (σ x) = (M.op (σ x) (σ y)) ∨ (k y x) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq113056
  have eq113355 : (σ (M.op x y)) ≠ (σ x) ∨ (k y x) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq113051
       grind)
    | exact superpose eq113051 eq16
    | exact resolve eq16 eq113051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113051
  have eq113855 : (σ x) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq113355
       have i₂ := eq101199
       grind)
    | exact superpose eq101199 eq113355
    | exact resolve eq113355 eq101199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113355
  have eq113864 : (σ x) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq113855
  have eq116847 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (k y x)) = (τ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq107208 x y
       have i₂ := eq12434
       grind)
    | exact superpose eq12434 eq107208
    | (have j0 := eq107208 x y
       grind)
    | exact resolve eq107208 eq12434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116866 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (τ (k y x)) = (τ x) ∨ (τ (M.op x x)) = (τ (k y x)) := by grind
  clear eq116847
  have eq118684 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X0))) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq90136 X0 X1
       grind)
    | exact superpose eq90136 eq10
    | (have j1 := eq90136 X0 X1
       grind)
    | exact resolve eq10 eq90136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90136
  have eq118720 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq118684 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq118684
    | (have j0 := eq118684 X0 X1
       grind)
    | exact resolve eq118684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118684
  have eq120155 : ∀ X0 X1 : G, (τ X1) = (τ (σ (k X0 (τ X1)))) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) (τ (σ X0)))) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq118720 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq118720
    | exact resolve eq118720 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120249 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq118720 X0 X1
       grind)
    | exact superpose eq118720 eq10
    | (have j1 := eq118720 X0 X1
       grind)
    | exact resolve eq10 eq118720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118720
  have eq120311 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq120249 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120249
    | (have j0 := eq120249 X0 X1
       grind)
    | exact resolve eq120249 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120249
  have eq120356 : ∀ X0 X1 : G, (τ X1) = (k X0 (τ X1)) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) (τ (σ X0)))) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq120155 X0 X1
       have i₂ := eq9 (k X0 (τ X1))
       grind)
    | exact superpose eq9 eq120155
    | (have j0 := eq120155 X0 X1
       grind)
    | exact resolve eq120155 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120155
  have eq120388 : ∀ X0 X1 : G, (τ X1) = (k X0 (τ X1)) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq120356 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq120356
    | (have j0 := eq120356 X0 X1
       grind)
    | exact resolve eq120356 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120356
  have eq120783 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op (τ X1) (τ (σ X0)))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq120311 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq120311
    | exact resolve eq120311 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120972 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X0))) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq120311 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120973 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op (τ X1) (τ X0))) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq120311 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120311
  have eq121115 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq120783 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq120783
    | (have j0 := eq120783 X0 X1
       grind)
    | exact resolve eq120783 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120783
  have eq121718 : ∀ X0 X1 : G, (σ (M.op (τ X1) X0)) ≠ X1 ∨ (k (σ X0) X1) = X1 ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq120972 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq120972
    | (have j0 := eq120972 (σ X0) X1
       grind)
    | exact resolve eq120972 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120972
  have eq121786 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = X1 ∨ (σ (M.op (τ X1) X0)) ≠ X1 ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq121718 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq121718
    | (have j0 := eq121718 X0 X1
       grind)
    | exact resolve eq121718 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121718
  have eq121800 : ∀ X0 X1 : G, (σ (M.op (τ X1) X0)) ≠ X1 ∨ (σ (k X0 (τ X1))) = X1 ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq121786 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq121786
    | (have j0 := eq121786 X0 X1
       grind)
    | exact resolve eq121786 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121786
  have eq122227 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op (τ X1) X0)) ∨ (k (σ X0) X1) = X1 ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq120973 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq120973
    | (have j0 := eq120973 (σ X0) X1
       grind)
    | exact resolve eq120973 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120973
  have eq122285 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = X1 ∨ (M.op X1 X1) ≠ (σ (M.op (τ X1) X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq122227 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq122227
    | (have j0 := eq122227 X0 X1
       grind)
    | exact resolve eq122227 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122227
  have eq122297 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op (τ X1) X0)) ∨ (σ (k X0 (τ X1))) = X1 ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq122285 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq122285
    | (have j0 := eq122285 X0 X1
       grind)
    | exact resolve eq122285 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122285
  have eq123902 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq121800 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq121800
    | exact resolve eq121800 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121800
  have eq123937 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq123902 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq123902
    | (have j0 := eq123902 X0 X1
       grind)
    | exact resolve eq123902 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123902
  have eq126889 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq122297 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq122297
    | exact resolve eq122297 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122297
  have eq126906 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq126889 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq126889
    | (have j0 := eq126889 X0 X1
       grind)
    | (have r₁ := eq126889 X0 X0
       have r₂ := eq62 X0
       grind)
    | exact resolve eq126889 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126889
  have eq126910 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq126906 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq126906
    | (have j0 := eq126906 X0 X1
       grind)
    | exact resolve eq126906 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126906
  have eq127850 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq126910 x y
       have i₂ := eq12434
       grind)
    | exact superpose eq12434 eq126910
    | (have j0 := eq126910 x y
       grind)
    | exact resolve eq126910 eq12434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126910
  have eq127871 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq127850
  have eq127880 : (σ x) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq88782 y x
       grind)
    | (have r₁ := eq127871
       have r₂ := eq88782 y x
       grind)
    | exact resolve eq127871 eq88782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88782 eq127871
  have eq128271 : (M.op x x) ≠ (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq127880
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq127880
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq127880 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128286 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq127880
       have i₂ := eq123 x y
       grind)
    | exact superpose eq123 eq127880
    | (have j1 := eq123 x y
       grind)
    | exact resolve eq127880 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq128318 : (τ (σ x)) = (k y x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq127880
       grind)
    | exact superpose eq127880 eq9
    | exact resolve eq9 eq127880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128383 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq127880
  have eq128387 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq128286
  have eq128390 : x = (k y x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq128318
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq128318
    | exact resolve eq128318 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128318
  have eq128801 : (M.op x x) ≠ (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128390
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq128390
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq128390 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128820 : (M.op x x) ≠ (M.op y y) ∨ x = (M.op x y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq128390
       grind)
    | exact superpose eq128390 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq128390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128886 : (σ x) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (τ (M.op x y)) = (τ x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq56635 x y
       have i₂ := eq128390
       grind)
    | exact superpose eq128390 eq56635
    | (have j0 := eq56635 x y
       grind)
    | exact resolve eq56635 eq128390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56635 eq128390
  have eq128896 : (M.op x y) = (M.op x x) ∨ (τ (M.op x y)) = (τ x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq128886
       have r₂ := eq128383
       grind)
    | exact resolve eq128886 eq128383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128886
  have eq132862 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (k y x)) = (τ x) ∨ (τ (M.op x y)) = (τ x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq107208 x y
       have i₂ := eq128896
       grind)
    | exact superpose eq128896 eq107208
    | (have j0 := eq107208 x y
       grind)
    | exact resolve eq107208 eq128896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132868 : (τ (M.op x x)) = (τ (k y x)) ∨ (τ (k y x)) = (τ x) ∨ (τ (M.op x y)) = (τ x) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq132862
  have eq132876 : (σ (k y x)) = (σ (M.op x x)) ∨ (τ (k y x)) = (τ x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have j1 := eq104245 x y
       grind)
    | (have r₁ := eq132868
       have r₂ := eq104245 x y
       grind)
    | exact resolve eq132868 eq104245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104245 eq132868
  have eq133904 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (M.op x y) = (M.op x x) ∨ (τ (k y x)) = (τ x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq61076 x y
       have i₂ := eq132876
       grind)
    | exact superpose eq132876 eq61076
    | (have j0 := eq61076 x y
       grind)
    | exact resolve eq61076 eq132876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132876
  have eq133936 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (M.op x y) = (M.op x x) ∨ (τ (k y x)) = (τ x) := by grind
  clear eq133904
  have eq134372 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq92785 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq92785
    | exact resolve eq92785 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92785
  have eq134568 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq134372 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq134372
    | (have j0 := eq134372 X0 X1
       grind)
    | exact resolve eq134372 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134372
  have eq134607 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq134568 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq134568
    | (have j0 := eq134568 X0 X1
       grind)
    | exact resolve eq134568 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134568
  have eq135678 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq134607 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134607
  have eq136195 : (σ x) ≠ (σ x) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq135678 y x
       have i₂ := eq113057
       grind)
    | exact superpose eq113057 eq135678
    | (have j0 := eq135678 y x
       grind)
    | (have r₁ := eq135678 y x
       have r₂ := eq113057
       grind)
    | exact resolve eq135678 eq113057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113057 eq135678
  have eq136198 : (σ x) ≠ (σ x) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq136195
  have eq136199 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq136198
  have eq136612 : (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq136199
       grind)
    | exact superpose eq136199 eq9
    | exact resolve eq9 eq136199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136199
  have eq136691 : x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq136612
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq136612
    | exact resolve eq136612 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136612
  have eq137375 : x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12434
       have i₂ := eq136691
       grind)
    | exact superpose eq136691 eq12434
    | exact resolve eq12434 eq136691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136691
  have eq137427 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq137375
       have r₂ := eq100178
       grind)
    | exact resolve eq137375 eq100178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137375
  have eq144133 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (σ X1)) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22868 X1 X0
       have i₂ := eq99701 X0 X1
       grind)
    | exact superpose eq99701 eq22868
    | (have j0 := eq22868 X1 X0
       have j1 := eq99701 X0 X1
       grind)
    | (have r₁ := eq22868 X1 (σ X1)
       have r₂ := eq99701 (σ X1) X1
       grind)
    | exact resolve eq22868 eq99701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22868 eq99701
  have eq144336 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq144133 X0 X1
       have j1 := eq114 X0 X1
       grind)
    | (have r₁ := eq144133 X0 X1
       have r₂ := eq114 X0 X1
       grind)
    | (have r₁ := eq144133 (σ X1) X1
       have r₂ := eq114 (σ X1) X1
       grind)
    | exact resolve eq144133 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq144133
  have eq144429 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 X0)) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq144336 X0 X1
       have j1 := eq86055 X0 X1
       grind)
    | (have r₁ := eq144336 X0 X1
       have r₂ := eq86055 X0 X1
       grind)
    | exact resolve eq144336 eq86055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86055 eq144336
  have eq153298 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X1)) ∨ (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (τ X1) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq144429 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144429
  have eq156739 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (M.op X0 X0))) ∨ (σ (k X1 (τ (σ X0)))) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (k X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq153298 X1 (σ X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq153298
    | (have j0 := eq153298 X1 (σ X0)
       grind)
    | exact resolve eq153298 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153298
  have eq156746 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (M.op X0 X0) ∨ (σ (k X1 (τ (σ X0)))) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (k X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq156739 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq156739
    | (have j0 := eq156739 X0 X1
       grind)
    | exact resolve eq156739 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156739
  have eq156749 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (σ (k X1 (τ (σ X0)))) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (k X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq156746 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq156746
    | (have j0 := eq156746 X0 X1
       grind)
    | exact resolve eq156746 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156746
  have eq156752 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X0 X0) ≠ X0 ∨ (τ (σ X0)) = (k X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq156749 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq156749
    | (have j0 := eq156749 X0 X1
       grind)
    | exact resolve eq156749 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156749
  have eq156755 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq156752 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq156752
    | (have j0 := eq156752 X0 X1
       grind)
    | exact resolve eq156752 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156752
  have eq156758 : x = (k y x) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j1 := eq156755 x y
       grind)
    | (have r₁ := eq93169
       have r₂ := eq156755 x x
       grind)
    | exact resolve eq93169 eq156755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93169 eq156755
  have eq166360 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (τ (k y x)) = (τ x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq116866
       grind)
    | exact superpose eq116866 eq16
    | exact resolve eq16 eq116866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116866
  have eq166435 : (M.op x y) = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have r₁ := eq133936
       have r₂ := eq166360
       grind)
    | exact resolve eq133936 eq166360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133936 eq166360
  have eq166821 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (k y x)) = (τ x) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq107208 x y
       have i₂ := eq166435
       grind)
    | exact superpose eq166435 eq107208
    | (have j0 := eq107208 x y
       grind)
    | exact resolve eq107208 eq166435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107208 eq166435
  have eq166828 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (k y x)) = (τ x) := by grind
  clear eq166821
  have eq166829 : (τ (k y x)) = (τ x) ∨ (τ (M.op x x)) = (τ (k y x)) := by grind
  clear eq166828
  have eq167146 : (τ (M.op x y)) = (τ x) ∨ (M.op x y) = (M.op x x) ∨ (τ (M.op x x)) = (τ x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq12306 y x
       have i₂ := eq166829
       grind)
    | exact superpose eq166829 eq12306
    | (have j0 := eq12306 y x
       grind)
    | exact resolve eq12306 eq166829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12306
  have eq167156 : (k y x) = (σ (τ x)) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq166829
       grind)
    | exact superpose eq166829 eq10
    | exact resolve eq10 eq166829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167233 : (τ (M.op x x)) ≠ (τ x) ∨ (τ (M.op x x)) = (τ (k y x)) := by grind
  clear eq166829
  have eq167240 : x = (k y x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq167156
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq167156
    | exact resolve eq167156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167156
  have eq167242 : (M.op x y) = (M.op x x) ∨ (τ (M.op x y)) = (τ x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have r₁ := eq167146
       have r₂ := eq167233
       grind)
    | exact resolve eq167146 eq167233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167146
  have eq167525 : (M.op x x) ≠ (M.op y y) ∨ x = (M.op x y) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq167240
       grind)
    | exact superpose eq167240 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq167240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167530 : (τ (M.op x x)) = (τ x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq222 y x
       have i₂ := eq167240
       grind)
    | exact superpose eq167240 eq222
    | (have j0 := eq222 y x
       grind)
    | exact resolve eq222 eq167240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq167602 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have r₁ := eq167530
       have r₂ := eq167233
       grind)
    | exact resolve eq167530 eq167233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167530
  have eq168678 : x ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) := by grind
  clear eq167602
  have eq195956 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq97790 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97790
    | exact resolve eq97790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97790
  have eq196077 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ (τ (M.op X0 X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq195956 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq195956
    | (have j0 := eq195956 X0 X1
       grind)
    | exact resolve eq195956 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195956
  have eq196525 : ∀ X0 X1 : G, (τ (M.op X1 X1)) ≠ (τ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (τ (M.op X1 X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq196077 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196077
  have eq196863 : (τ (σ (M.op x x))) ≠ (τ (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (τ (k (σ y) (σ x))) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq196525 (σ y) (σ x)
       have i₂ := eq137427
       grind)
    | exact superpose eq137427 eq196525
    | (have j0 := eq196525 (σ y) (σ x)
       grind)
    | exact resolve eq196525 eq137427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137427 eq196525
  have eq196937 : (τ (σ (M.op x x))) ≠ (τ (σ (M.op x x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (τ (k (σ y) (σ x))) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq196863
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq196863
    | exact resolve eq196863 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196863
  have eq196938 : (σ x) = (k (σ y) (σ x)) ∨ (τ (k (σ y) (σ x))) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq196937
  have eq196961 : (σ x) = (σ (k y (τ (σ x)))) ∨ (τ (k (σ y) (σ x))) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq196938
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq196938
    | exact resolve eq196938 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196938
  have eq196981 : (σ x) = (σ (k y x)) ∨ (τ (k (σ y) (σ x))) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq196961
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq196961
    | exact resolve eq196961 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196961
  have eq196982 : (σ x) = (σ (k y x)) ∨ (τ (k (σ y) (σ x))) = (τ (M.op (σ x) (σ x))) ∨ (k y x) = (M.op x x) := by grind
  clear eq196981
  have eq197004 : (τ (σ (M.op x x))) = (τ (k (σ y) (σ x))) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq196982
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq196982
    | exact resolve eq196982 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196982
  have eq197014 : (τ (σ (M.op x x))) = (τ (σ (k y (τ (σ x))))) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq197004
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq197004
    | exact resolve eq197004 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197004
  have eq197022 : (k y (τ (σ x))) = (τ (σ (M.op x x))) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq197014
       have i₂ := eq9 (k y (τ (σ x)))
       grind)
    | exact superpose eq9 eq197014
    | exact resolve eq197014 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197014
  have eq197028 : (k y (τ (σ x))) = (M.op x x) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq197022
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq197022
    | exact resolve eq197022 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197022
  have eq197035 : (k y x) = (M.op x x) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq197028
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq197028
    | exact resolve eq197028 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197028
  have eq197036 : (k y x) = (M.op x x) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq197035
  have eq197477 : (M.op x x) ≠ (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq197036
       grind)
    | exact superpose eq197036 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq197036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197036
  have eq202150 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq120388 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq120388
    | exact resolve eq120388 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120388
  have eq202254 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq202150 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq202150
    | (have j0 := eq202150 X0 X1
       grind)
    | exact resolve eq202150 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202150
  have eq202682 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (k X0 (τ X1)))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (σ (σ (k X0 (τ X1)))) = (σ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq202254 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq202254
    | exact resolve eq202254 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202769 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq202254 X0 X1
       grind)
    | exact superpose eq202254 eq9
    | (have j1 := eq202254 X0 X1
       grind)
    | exact resolve eq9 eq202254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202792 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq202254 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202254
  have eq202805 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq202769 X0 X1
       have i₂ := eq9 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq202769
    | (have j0 := eq202769 X0 X1
       grind)
    | exact resolve eq202769 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202769
  have eq203268 : ∀ X0 X1 : G, (σ (τ (k X0 (σ X1)))) = (σ (M.op X1 X1)) ∨ (τ (k X0 (σ X1))) = X1 ∨ (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq202805 X1 (τ X0)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq202805
    | exact resolve eq202805 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202805
  have eq203443 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (τ (k X0 (σ X1))) = X1 ∨ (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq203268 X0 X1
       have i₂ := eq10 (k X0 (σ X1))
       grind)
    | exact superpose eq10 eq203268
    | (have j0 := eq203268 X0 X1
       grind)
    | exact resolve eq203268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203268
  have eq203830 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) ≠ (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k X1 (τ X0)) ∨ (σ (k X1 (τ X0))) = (σ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq202792 X0 (τ X0)
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq202792
    | (have j0 := eq202792 X1 (τ X0)
       grind)
    | exact resolve eq202792 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202792
  have eq203966 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k X1 (τ X0)) ∨ (σ (k X1 (τ X0))) = (σ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq203830 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq203830
    | (have j0 := eq203830 X0 X1
       grind)
    | exact resolve eq203830 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203830
  have eq203993 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (σ (k X1 (τ X0))) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq203966 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq203966
    | (have j0 := eq203966 X0 X1
       grind)
    | exact resolve eq203966 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203966
  have eq207878 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (τ (k X1 X0)) ∨ (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq203443 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq203443
    | exact resolve eq203443 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203443
  have eq208012 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X0))) ∨ (τ X0) = (τ (k X1 X0)) ∨ (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq207878 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq207878
    | (have j0 := eq207878 X0 X1
       grind)
    | exact resolve eq207878 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207878
  have eq208031 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) ∨ (τ X0) = (τ (k X1 X0)) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq208012 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq208012
    | (have j0 := eq208012 X0 X1
       grind)
    | exact resolve eq208012 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208012
  have eq208418 : ∀ X0 X1 : G, (τ X1) ≠ (M.op (τ X1) (τ X0)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq208031 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208031
  have eq208856 : (τ x) ≠ (τ x) ∨ (τ (k y x)) = (τ x) ∨ (k y x) = (M.op x x) ∨ (τ (M.op x x)) = (M.op (τ x) (τ y)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq208418 y x
       have i₂ := eq100202
       grind)
    | exact superpose eq100202 eq208418
    | (have j0 := eq208418 y x
       grind)
    | (have r₁ := eq208418 y x
       have r₂ := eq100202
       grind)
    | exact resolve eq208418 eq100202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100202 eq208418
  have eq208861 : (τ x) ≠ (τ x) ∨ (τ (k y x)) = (τ x) ∨ (k y x) = (M.op x x) ∨ (τ (M.op x x)) = (M.op (τ x) (τ y)) := by grind
  clear eq208856
  have eq208862 : (τ (M.op x x)) = (M.op (τ x) (τ y)) ∨ (k y x) = (M.op x x) ∨ (τ (k y x)) = (τ x) := by grind
  clear eq208861
  have eq210410 : (M.op x x) ≠ (σ (τ (M.op x x))) ∨ (M.op x x) = (σ (k (τ y) (τ x))) ∨ (τ x) = (k (τ y) (τ x)) ∨ (k y x) = (M.op x x) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq203993 x (τ y)
       have i₂ := eq208862
       grind)
    | exact superpose eq208862 eq203993
    | (have j0 := eq203993 x (τ y)
       grind)
    | exact resolve eq203993 eq208862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203993 eq208862
  have eq210471 : (M.op x x) = (σ (k (τ y) (τ x))) ∨ (τ x) = (k (τ y) (τ x)) ∨ (k y x) = (M.op x x) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have r₁ := eq210410
       have r₂ := eq10 (M.op x x)
       grind)
    | exact resolve eq210410 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210410
  have eq210495 : (M.op x x) = (σ (τ (k y (σ (τ x))))) ∨ (τ x) = (k (τ y) (τ x)) ∨ (k y x) = (M.op x x) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq210471
       have i₂ := eq22 y (τ x)
       grind)
    | exact superpose eq22 eq210471
    | exact resolve eq210471 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210471
  have eq210517 : (M.op x x) = (k y (σ (τ x))) ∨ (τ x) = (k (τ y) (τ x)) ∨ (k y x) = (M.op x x) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq210495
       have i₂ := eq10 (k y (σ (τ x)))
       grind)
    | exact superpose eq10 eq210495
    | exact resolve eq210495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210495
  have eq210534 : (k y x) = (M.op x x) ∨ (τ x) = (k (τ y) (τ x)) ∨ (k y x) = (M.op x x) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq210517
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq210517
    | exact resolve eq210517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210517
  have eq210535 : (k y x) = (M.op x x) ∨ (τ x) = (k (τ y) (τ x)) ∨ (τ (k y x)) = (τ x) := by grind
  clear eq210534
  have eq210548 : (τ x) = (τ (k y (σ (τ x)))) ∨ (k y x) = (M.op x x) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq210535
       have i₂ := eq22 y (τ x)
       grind)
    | exact superpose eq22 eq210535
    | exact resolve eq210535 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210535
  have eq210559 : (τ (k y x)) = (τ x) ∨ (k y x) = (M.op x x) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq210548
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq210548
    | exact resolve eq210548 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210548
  have eq210560 : (k y x) = (M.op x x) ∨ (τ (k y x)) = (τ x) := by grind
  clear eq210559
  have eq211048 : (M.op x x) ≠ (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq210560
       grind)
    | exact superpose eq210560 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq210560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210560
  have eq216451 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (M.op (σ X1) X0)) ∨ (τ (k X0 (σ X1))) = X1 ∨ (τ (k X0 (σ X1))) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq98418 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98418
  have eq220281 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq121115 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq121115
    | exact resolve eq121115 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220358 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op (τ X1) X0)) ∨ (σ (k X0 (τ X1))) = X1 ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq121115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121115
  have eq220397 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq220281 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq220281
    | (have j0 := eq220281 X0 X1
       grind)
    | exact resolve eq220281 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220281
  have eq221682 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq220397 X0 X1
       grind)
    | exact superpose eq220397 eq9
    | (have j1 := eq220397 X0 X1
       grind)
    | exact resolve eq9 eq220397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220397
  have eq221709 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq221682 X0 X1
       have i₂ := eq9 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq221682
    | (have j0 := eq221682 X0 X1
       grind)
    | exact resolve eq221682 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221682
  have eq222133 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq221709 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221709
  have eq234727 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) ≠ (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X1 X0)) ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq216451 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq216451
    | exact resolve eq216451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216451
  have eq234765 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X1 X0)) ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq234727 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq234727
    | (have j0 := eq234727 X0 X1
       grind)
    | (have r₁ := eq234727 X0 X0
       have r₂ := eq90 X0
       grind)
    | exact resolve eq234727 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234727
  have eq239237 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq220358 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq220358
    | exact resolve eq220358 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220358
  have eq239262 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq239237 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq239237
    | (have j0 := eq239237 X0 X1
       grind)
    | (have r₁ := eq239237 X0 X0
       have r₂ := eq62 X0
       grind)
    | exact resolve eq239237 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239237
  have eq253138 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq128387
       grind)
    | exact superpose eq128387 eq16
    | exact resolve eq16 eq128387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128387
  have eq254032 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq253138
       have i₂ := eq128896
       grind)
    | exact superpose eq128896 eq253138
    | exact resolve eq253138 eq128896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128896 eq253138
  have eq254053 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by grind
  clear eq254032
  have eq254054 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by grind
  clear eq254053
  have eq254326 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq254054
       grind)
    | exact superpose eq254054 eq16
    | exact resolve eq16 eq254054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254368 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq254054
       grind)
    | exact superpose eq254054 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq254054
       grind)
    | exact resolve eq12 eq254054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254054
  have eq254401 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by grind
  clear eq254368
  have eq254437 : (M.op (σ x) (σ x)) = (σ (k y (τ (σ x)))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq254401
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq254401
    | exact resolve eq254401 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254401
  have eq254480 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq254437
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq254437
    | exact resolve eq254437 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254437
  have eq254520 : (σ (k y x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq254480
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq254480
    | exact resolve eq254480 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254480
  have eq254521 : (σ (k y x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (τ (M.op x y)) = (τ x) := by grind
  clear eq254520
  have eq254555 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq254521
       have i₂ := eq62 y
       grind)
    | exact superpose eq62 eq254521
    | exact resolve eq254521 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254521
  have eq254585 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq254555
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq254555
    | exact resolve eq254555 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254555
  have eq258427 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq254585
       grind)
    | exact superpose eq254585 eq9
    | exact resolve eq9 eq254585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254585
  have eq258449 : (M.op x x) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq258427
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq258427
    | exact resolve eq258427 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258427
  have eq259161 : (M.op x x) ≠ (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq128271
       have i₂ := eq258449
       grind)
    | exact superpose eq258449 eq128271
    | (have r₁ := eq128271
       have r₂ := eq258449
       grind)
    | exact resolve eq128271 eq258449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128271
  have eq259163 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq128820
       have i₂ := eq258449
       grind)
    | exact superpose eq258449 eq128820
    | (have r₁ := eq128820
       have r₂ := eq258449
       grind)
    | exact resolve eq128820 eq258449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128820 eq258449
  have eq259475 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by grind
  clear eq259163
  have eq259476 : x = (M.op x y) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by grind
  clear eq259475
  have eq259478 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by grind
  clear eq259161
  have eq259500 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have r₁ := eq259478
       have r₂ := eq254326
       grind)
    | exact resolve eq259478 eq254326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254326 eq259478
  have eq260232 : x = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x x) = (M.op y y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq259476
       have i₂ := eq101199
       grind)
    | exact superpose eq101199 eq259476
    | exact resolve eq259476 eq101199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101199
  have eq260248 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq12434
       have i₂ := eq259476
       grind)
    | exact superpose eq259476 eq12434
    | exact resolve eq12434 eq259476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259476
  have eq260320 : (k y x) = (M.op x x) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x x) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq260232
       have r₂ := eq100178
       grind)
    | exact resolve eq260232 eq100178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260232
  have eq440294 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (τ (M.op (σ (σ X0)) (σ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq98079 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq98079
    | exact resolve eq98079 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98079
  have eq440308 : ∀ X0 X1 : G, (σ (k X1 X0)) = (τ (M.op (σ (σ X0)) (σ (σ X1)))) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq440294 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq440294
    | (have j0 := eq440294 X0 X1
       grind)
    | exact resolve eq440294 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440294
  have eq440948 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (τ (τ (M.op (σ (σ X0)) (σ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq440308 X0 X1
       grind)
    | exact superpose eq440308 eq9
    | (have j1 := eq440308 X0 X1
       grind)
    | exact resolve eq9 eq440308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440308
  have eq442163 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (τ (τ (M.op (σ (σ X0)) (σ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq440948 X0 X1
       grind)
    | exact superpose eq440948 eq9
    | (have j1 := eq440948 X0 X1
       grind)
    | exact resolve eq9 eq440948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440948
  have eq442169 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (τ (τ (M.op (σ (σ X0)) (σ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq442163 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq442163
    | (have j0 := eq442163 X0 X1
       grind)
    | exact resolve eq442163 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442163
  have eq442234 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (τ (τ (M.op (σ (σ X0)) (σ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq442169 X0 X1
       grind)
    | exact superpose eq442169 eq9
    | (have j1 := eq442169 X0 X1
       grind)
    | exact resolve eq9 eq442169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442169
  have eq442248 : ∀ X0 X1 : G, (k X1 X0) = (τ (τ (M.op (σ (σ X0)) (σ (σ X1))))) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq442234 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq442234
    | (have j0 := eq442234 X0 X1
       grind)
    | exact resolve eq442234 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442234
  have eq442260 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (τ (τ (M.op (σ (σ X1)) (σ (σ (τ X0)))))) ∨ (M.op X1 X1) = (τ (k X0 (σ X1))) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq442248 X1 (τ X0)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq442248
    | exact resolve eq442248 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442248
  have eq442288 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k X0 (σ X1))) ∨ (τ (k X0 (σ X1))) = (τ (τ (M.op (σ (σ X1)) (σ X0)))) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq442260 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq442260
    | (have j0 := eq442260 X0 X1
       grind)
    | exact resolve eq442260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442260
  have eq450305 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X1 (σ X0))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (σ (σ (k X0 (τ X1)))) = (σ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq202682 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202682
  have eq450323 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X1 X0)) ∨ (σ (k (τ X0) (τ X1))) = X1 ∨ (σ (σ (k (τ X0) (τ X1)))) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq450305 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq450305
    | (have j0 := eq450305 (τ X0) X1
       grind)
    | exact resolve eq450305 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450305
  have eq450332 : ∀ X0 X1 : G, (σ (τ (k X0 (σ (τ X1))))) = X1 ∨ (σ (M.op X1 X1)) ≠ (σ (M.op X1 X0)) ∨ (σ (σ (k (τ X0) (τ X1)))) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq450323 X0 X1
       have i₂ := eq22 X0 (τ X1)
       grind)
    | exact superpose eq22 eq450323
    | (have j0 := eq450323 X0 X1
       grind)
    | exact resolve eq450323 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450323
  have eq450337 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = X1 ∨ (σ (M.op X1 X1)) ≠ (σ (M.op X1 X0)) ∨ (σ (σ (k (τ X0) (τ X1)))) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq450332 X0 X1
       have i₂ := eq10 (k X0 (σ (τ X1)))
       grind)
    | exact superpose eq10 eq450332
    | (have j0 := eq450332 X0 X1
       grind)
    | exact resolve eq450332 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450332
  have eq450341 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (σ (M.op X1 X1)) ≠ (σ (M.op X1 X0)) ∨ (σ (σ (k (τ X0) (τ X1)))) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq450337 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq450337
    | (have j0 := eq450337 X0 X1
       grind)
    | exact resolve eq450337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450337
  have eq450343 : ∀ X0 X1 : G, (σ (σ (τ (k X0 (σ (τ X1)))))) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (σ (M.op X1 X1)) ≠ (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq450341 X0 X1
       have i₂ := eq22 X0 (τ X1)
       grind)
    | exact superpose eq22 eq450341
    | (have j0 := eq450341 X0 X1
       grind)
    | exact resolve eq450341 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450341
  have eq450344 : ∀ X0 X1 : G, (σ (k X0 (σ (τ X1)))) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (σ (M.op X1 X1)) ≠ (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq450343 X0 X1
       have i₂ := eq10 (k X0 (σ (τ X1)))
       grind)
    | exact superpose eq10 eq450343
    | (have j0 := eq450343 X0 X1
       grind)
    | exact resolve eq450343 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450343
  have eq450345 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq450344 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq450344
    | (have j0 := eq450344 X0 X1
       grind)
    | exact resolve eq450344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450344
  have eq458054 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X1 X0)) ∨ (τ (k X1 X0)) = (τ (τ (M.op (σ X0) (σ X1)))) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq442288 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq442288
    | exact resolve eq442288 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442288
  have eq458068 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (τ (M.op (σ X0) (σ X1)))) ∨ (τ (M.op X0 X0)) = (τ (k X1 X0)) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq458054 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq458054
    | (have j0 := eq458054 X0 X1
       grind)
    | exact resolve eq458054 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458054
  have eq458095 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (τ (M.op (σ X0) (σ X1))))) ∨ (τ (M.op X0 X0)) = (τ (k X1 X0)) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq458068 X0 X1
       grind)
    | exact superpose eq458068 eq10
    | (have j1 := eq458068 X0 X1
       grind)
    | exact resolve eq10 eq458068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458068
  have eq458102 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X1 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq458095 X0 X1
       have i₂ := eq10 (τ (M.op (σ X0) (σ X1)))
       grind)
    | exact superpose eq10 eq458095
    | (have j0 := eq458095 X0 X1
       grind)
    | exact resolve eq458095 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458095
  have eq458131 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X0))) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq458102 X0 X1
       grind)
    | exact superpose eq458102 eq10
    | (have j1 := eq458102 X0 X1
       grind)
    | exact resolve eq10 eq458102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458102
  have eq458137 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq458131 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq458131
    | (have j0 := eq458131 X0 X1
       grind)
    | exact resolve eq458131 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458131
  have eq458161 : ∀ X0 X1 : G, (τ X1) = (τ (τ (k X0 (σ X1)))) ∨ (τ (k X0 (σ X1))) = (τ (M.op (σ X1) (σ (τ X0)))) ∨ (M.op X1 X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq458137 X1 (τ X0)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq458137
    | exact resolve eq458137 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458137
  have eq458228 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k X0 (σ X1))) ∨ (τ X1) = (τ (τ (k X0 (σ X1)))) ∨ (τ (k X0 (σ X1))) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq458161 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq458161
    | (have j0 := eq458161 X0 X1
       grind)
    | exact resolve eq458161 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458161
  have eq458607 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X1 X0)) ∨ (τ (τ X0)) = (τ (τ (k X1 X0))) ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq458228 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq458228
    | exact resolve eq458228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458228
  have eq458615 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (τ (τ X0)) = (τ (τ (k X1 X0))) ∨ (τ (M.op X0 X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq458607 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq458607
    | (have j0 := eq458607 X0 X1
       grind)
    | exact resolve eq458607 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458607
  have eq458634 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (τ (τ X0)) = (τ (τ (k X1 X0))) ∨ (τ (M.op X0 X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq458615 X0 X1
       grind)
    | exact superpose eq458615 eq10
    | (have j1 := eq458615 X0 X1
       grind)
    | exact resolve eq10 eq458615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458615
  have eq458640 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X1 X0)) ∨ (τ (τ X0)) = (τ (τ (k X1 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq458634 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq458634
    | (have j0 := eq458634 X0 X1
       grind)
    | exact resolve eq458634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458634
  have eq458674 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X0))) ∨ (τ (τ X0)) = (τ (τ (k X1 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq458640 X0 X1
       grind)
    | exact superpose eq458640 eq10
    | (have j1 := eq458640 X0 X1
       grind)
    | exact resolve eq10 eq458640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458640
  have eq458680 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ (τ X0)) = (τ (τ (k X1 X0))) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq458674 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq458674
    | (have j0 := eq458674 X0 X1
       grind)
    | exact resolve eq458674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458674
  have eq458686 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k X0 (σ X1))) ∨ (τ (τ X1)) = (τ (τ (τ (k X0 (σ X1))))) ∨ (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq458680 X1 (τ X0)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq458680
    | exact resolve eq458680 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq458680
  have eq464641 : x = (M.op x x) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq260320
       have i₂ := eq99655
       grind)
    | exact superpose eq99655 eq260320
    | exact resolve eq260320 eq99655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260320
  have eq464649 : x = (M.op x x) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x x) = (M.op y y) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq464641
       have r₂ := eq113864
       grind)
    | exact resolve eq464641 eq113864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464641
  have eq464650 : (k y x) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have r₁ := eq464649
       have r₂ := eq100178
       grind)
    | exact resolve eq464649 eq100178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464649
  have eq464654 : x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (τ (M.op x x)) = (τ x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq464650
       have i₂ := eq167240
       grind)
    | exact superpose eq167240 eq464650
    | exact resolve eq464650 eq167240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167240 eq464650
  have eq464683 : (M.op x x) = (M.op y y) ∨ x = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have r₁ := eq464654
       have r₂ := eq167233
       grind)
    | exact resolve eq464654 eq167233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464654
  have eq464692 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ x = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq167525
       have i₂ := eq464683
       grind)
    | exact superpose eq464683 eq167525
    | (have r₁ := eq167525
       have r₂ := eq464683
       grind)
    | exact resolve eq167525 eq464683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167525
  have eq464733 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (M.op x x) ∨ (k y (σ X0)) = (M.op (σ X0) y) ∨ x = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq189 y X0
       have i₂ := eq464683
       grind)
    | exact superpose eq464683 eq189
    | (have j0 := eq189 x X0
       grind)
    | exact resolve eq189 eq464683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq464683
  have eq464999 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ x = (M.op x x) := by grind
  clear eq464692
  have eq465000 : x = (M.op x y) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ x = (M.op x x) := by grind
  clear eq464999
  have eq465085 : x = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ x = (M.op x x) ∨ (τ (M.op x y)) = (τ x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq465000
       have i₂ := eq167242
       grind)
    | exact superpose eq167242 eq465000
    | exact resolve eq465000 eq167242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167242 eq465000
  have eq465279 : x = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (M.op x y)) = (τ x) := by grind
  clear eq465085
  have eq466660 : (τ x) ≠ (τ x) ∨ (τ x) = (τ (k x x)) ∨ (τ x) = (τ (k x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq234765 x x
       have i₂ := eq465279
       grind)
    | exact superpose eq465279 eq234765
    | (have j0 := eq234765 x x
       grind)
    | exact resolve eq234765 eq465279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234765 eq465279
  have eq466690 : (τ x) ≠ (τ x) ∨ (τ x) = (τ (k x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (M.op x y)) = (τ x) := by grind
  clear eq466660
  have eq466691 : (τ x) = (τ (k x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (M.op x y)) = (τ x) := by grind
  clear eq466690
  have eq466858 : (τ (M.op x x)) = (τ x) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq466691
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq466691
    | exact resolve eq466691 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466691
  have eq466888 : (τ (M.op x y)) = (τ x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have r₁ := eq466858
       have r₂ := eq167233
       grind)
    | exact resolve eq466858 eq167233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466858
  have eq466899 : (τ (M.op x x)) = (τ x) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq466888
       have i₂ := eq12434
       grind)
    | exact superpose eq12434 eq466888
    | exact resolve eq466888 eq12434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12434 eq466888
  have eq467094 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have r₁ := eq466899
       have r₂ := eq167233
       grind)
    | exact resolve eq466899 eq167233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167233 eq466899
  have eq467551 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq467094
       grind)
    | exact superpose eq467094 eq16
    | exact resolve eq16 eq467094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467094
  have eq471875 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 X0)) ∨ (τ (τ X0)) = (τ (τ (τ (k X1 (σ X0))))) ∨ (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (σ X0))
       have i₂ := eq458686 X1 X0
       grind)
    | exact superpose eq458686 eq10
    | (have j1 := eq458686 X1 X0
       grind)
    | exact resolve eq10 eq458686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458686
  have eq472095 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ (τ (τ X0))) = (τ (τ (τ (k X1 X0)))) ∨ (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq471875 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq471875
    | exact resolve eq471875 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471875
  have eq472105 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X0))) ∨ (τ (τ (τ X0))) = (τ (τ (τ (k X1 X0)))) ∨ (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq472095 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq472095
    | (have j0 := eq472095 X0 X1
       grind)
    | exact resolve eq472095 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472095
  have eq472109 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) ∨ (τ (τ (τ X0))) = (τ (τ (τ (k X1 X0)))) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq472105 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq472105
    | (have j0 := eq472105 X0 X1
       grind)
    | exact resolve eq472105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472105
  have eq472153 : ∀ X0 X1 : G, (τ (τ (τ X0))) = (τ (τ (τ (k X1 X0)))) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq472109 X0 X1
       grind)
    | exact superpose eq472109 eq10
    | (have j1 := eq472109 X0 X1
       grind)
    | exact resolve eq10 eq472109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472109
  have eq472164 : ∀ X0 X1 : G, (τ (τ (k X1 X0))) = (σ (τ (τ (τ X0)))) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ (τ (k X1 X0)))
       have i₂ := eq472153 X0 X1
       grind)
    | exact superpose eq472153 eq10
    | (have j1 := eq472153 X0 X1
       grind)
    | exact resolve eq10 eq472153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472153
  have eq472167 : ∀ X0 X1 : G, (τ (τ X0)) = (τ (τ (k X1 X0))) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq472164 X0 X1
       have i₂ := eq10 (τ (τ X0))
       grind)
    | exact superpose eq10 eq472164
    | (have j0 := eq472164 X0 X1
       grind)
    | exact resolve eq472164 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472164
  have eq472176 : ∀ X0 X1 : G, (τ (τ X1)) = (τ (τ (σ (k X0 (τ X1))))) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) (τ (σ X0)))) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq472167 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq472167
    | exact resolve eq472167 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq472167
  have eq472189 : ∀ X0 X1 : G, (τ (τ X1)) = (τ (k X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) (τ (σ X0)))) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq472176 X0 X1
       have i₂ := eq9 (k X0 (τ X1))
       grind)
    | exact superpose eq9 eq472176
    | (have j0 := eq472176 X0 X1
       grind)
    | exact resolve eq472176 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472176
  have eq472192 : ∀ X0 X1 : G, (τ (τ X1)) = (τ (k X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) ∨ (M.op X1 X1) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq472189 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq472189
    | (have j0 := eq472189 X0 X1
       grind)
    | exact resolve eq472189 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472189
  have eq472215 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq472192 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq472192
    | exact resolve eq472192 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472192
  have eq472226 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (τ X0) = (τ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq472215 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq472215
    | (have j0 := eq472215 X0 X1
       grind)
    | exact resolve eq472215 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq472215
  have eq472254 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X1 X0)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq472226 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472226
  have eq485584 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq260248
       grind)
    | exact superpose eq260248 eq16
    | exact resolve eq16 eq260248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260248
  have eq485585 : x = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have r₁ := eq485584
       have r₂ := eq259500
       grind)
    | exact resolve eq485584 eq259500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259500 eq485584
  have eq485715 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq123937 x x
       have i₂ := eq485585
       grind)
    | exact superpose eq485585 eq123937
    | (have j0 := eq123937 x y
       grind)
    | exact resolve eq123937 eq485585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123937 eq485585
  have eq485752 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by grind
  clear eq485715
  have eq485753 : (σ x) = (σ (k x x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by grind
  clear eq485752
  have eq485857 : (σ x) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (τ (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq485753
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq485753
    | exact resolve eq485753 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485753
  have eq485879 : (τ (M.op x y)) = (τ x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq485857
       have r₂ := eq128383
       grind)
    | exact resolve eq485857 eq128383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128383 eq485857
  have eq485958 : (M.op x y) = (σ (τ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq485879
       grind)
    | exact superpose eq485879 eq10
    | exact resolve eq10 eq485879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485879
  have eq486018 : x = (M.op x y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq485958
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq485958
    | exact resolve eq485958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485958
  have eq486146 : x ≠ x ∨ (k y x) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq486018
       grind)
    | exact superpose eq486018 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq486018
       grind)
    | exact resolve eq12 eq486018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486018
  have eq486255 : (k y x) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq486146
  have eq487548 : x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq486255
       have i₂ := eq99655
       grind)
    | exact superpose eq99655 eq486255
    | exact resolve eq486255 eq99655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99655 eq486255
  have eq487561 : x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq487548
       have r₂ := eq113864
       grind)
    | exact resolve eq487548 eq113864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113864 eq487548
  have eq487562 : (k y x) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq487561
       have r₂ := eq100178
       grind)
    | exact resolve eq487561 eq100178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100178 eq487561
  have eq494382 : ∀ X0 : G, (M.op x x) ≠ (σ (τ (M.op X0 X0))) ∨ (k y (σ (τ X0))) = (M.op (σ (τ X0)) y) ∨ x = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq464733 (τ X0)
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq464733
    | (have j0 := eq464733 (τ X0)
       grind)
    | exact resolve eq464733 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq464733
  have eq494383 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y (σ (τ X0))) = (M.op (σ (τ X0)) y) ∨ x = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq494382 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq494382
    | (have j0 := eq494382 X0
       grind)
    | (have r₁ := eq494382 x
       have r₂ := eq10 (M.op x x)
       grind)
    | exact resolve eq494382 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494382
  have eq494384 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq494383 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq494383
    | (have j0 := eq494383 X0
       grind)
    | exact resolve eq494383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494383
  have eq494387 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have j0 := eq494384 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494384
  have eq494458 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq487562
       have i₂ := eq494387
       grind)
    | exact superpose eq494387 eq487562
    | exact resolve eq487562 eq494387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487562 eq494387
  have eq494478 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have r₁ := eq494458
       have r₂ := eq168678
       grind)
    | exact resolve eq494458 eq168678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168678 eq494458
  have eq494510 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq467551
       have i₂ := eq494478
       grind)
    | exact superpose eq494478 eq467551
    | exact resolve eq467551 eq494478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494478
  have eq494536 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq494510
  have eq494537 : (M.op x x) = (M.op y y) ∨ (τ (M.op x x)) = (τ (k y x)) := by grind
  clear eq494536
  have eq494602 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq101 X0 y
       have i₂ := eq494537
       grind)
    | exact superpose eq494537 eq101
    | (have j0 := eq101 X0 x
       grind)
    | exact resolve eq101 eq494537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494537
  have eq496984 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have j0 := eq494602 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494602
  have eq496999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (M.op x x)) = (τ (M.op x y)) ∨ (M.op x x) ≠ (M.op y y) := by
    first
    | (have i₁ := eq496984
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq496984
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq496984 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497097 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (M.op x y) = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq61076 x y
       have i₂ := eq496984
       grind)
    | exact superpose eq496984 eq61076
    | (have j0 := eq61076 x y
       grind)
    | exact resolve eq61076 eq496984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61076 eq496984
  have eq497137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq497097
  have eq497150 : (M.op x y) = (M.op x x) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have r₁ := eq497137
       have r₂ := eq16
       grind)
    | exact resolve eq497137 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497137
  have eq497156 : (M.op x x) ≠ (M.op y y) ∨ (τ (M.op x x)) = (τ (M.op x y)) := by
    first
    | (have r₁ := eq496999
       have r₂ := eq16
       grind)
    | exact resolve eq496999 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496999
  have eq497260 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq467551
       have i₂ := eq497150
       grind)
    | exact superpose eq497150 eq467551
    | exact resolve eq467551 eq497150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467551 eq497150
  have eq497377 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) := by grind
  clear eq497260
  have eq497378 : (τ (M.op x x)) = (τ (k y x)) := by grind
  clear eq497377
  have eq497538 : (M.op x x) ≠ (M.op y y) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq211048
       have i₂ := eq497378
       grind)
    | exact superpose eq497378 eq211048
    | exact resolve eq211048 eq497378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211048
  have eq498253 : (τ (M.op x x)) = (τ x) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq497378
       have i₂ := eq156758
       grind)
    | exact superpose eq156758 eq497378
    | exact resolve eq497378 eq156758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156758
  have eq498501 : (k y x) = (σ (τ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq497378
       grind)
    | exact superpose eq497378 eq10
    | exact resolve eq10 eq497378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497378
  have eq498703 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq498501
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq498501
    | exact resolve eq498501 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498501
  have eq498985 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12701
       have i₂ := eq498703
       grind)
    | exact superpose eq498703 eq12701
    | exact resolve eq12701 eq498703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12701
  have eq498987 : x = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq13153
       have i₂ := eq498703
       grind)
    | exact superpose eq498703 eq13153
    | exact resolve eq13153 eq498703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13153
  have eq499111 : (M.op x x) ≠ (M.op y y) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq197477
       have i₂ := eq498703
       grind)
    | exact superpose eq498703 eq197477
    | exact resolve eq197477 eq498703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197477
  have eq499554 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq498253
       have i₂ := eq498703
       grind)
    | exact superpose eq498703 eq498253
    | exact resolve eq498253 eq498703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498253
  have eq499700 : x = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq498987
  have eq499702 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq498985
  have eq499967 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq499554
       have i₂ := eq498703
       grind)
    | exact superpose eq498703 eq499554
    | exact resolve eq499554 eq498703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499554
  have eq500125 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq499700
       have i₂ := eq498703
       grind)
    | exact superpose eq498703 eq499700
    | exact resolve eq499700 eq498703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499700
  have eq500126 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq500125
  have eq500219 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq499967
       have r₂ := eq499702
       grind)
    | exact resolve eq499967 eq499702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499967
  have eq500358 : (M.op x x) ≠ (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq498703
       grind)
    | exact superpose eq498703 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq498703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500675 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq500219
       grind)
    | exact superpose eq500219 eq16
    | exact resolve eq16 eq500219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500219
  have eq500825 : (σ x) ≠ (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq500675
       have i₂ := eq17 y x
       grind)
    | exact superpose eq17 eq500675
    | (have j1 := eq17 y x
       grind)
    | exact resolve eq500675 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500828 : (σ x) ≠ (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq500825
       have r₂ := eq497538
       grind)
    | exact resolve eq500825 eq497538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497538 eq500825
  have eq500829 : (M.op x y) = (M.op x x) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq500828
       have i₂ := eq498703
       grind)
    | exact superpose eq498703 eq500828
    | exact resolve eq500828 eq498703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500828
  have eq500830 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (τ (M.op x x)) = (τ x) := by grind
  clear eq500829
  have eq500879 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (σ (k X0 x)) ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq222133 X0 x
       have i₂ := eq500126
       grind)
    | exact superpose eq500126 eq222133
    | (have j0 := eq222133 X0 x
       grind)
    | (have r₁ := eq222133 X0 x
       have r₂ := eq500126
       grind)
    | exact resolve eq222133 eq500126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500126
  have eq500921 : ∀ X0 : G, (σ x) = (σ (k X0 x)) ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq500879 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500879
  have eq500950 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (σ (k X0 x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq500921 X0
       have j1 := eq222133 X0 x
       grind)
    | (have r₁ := eq500921 X0
       have r₂ := eq222133 X0 x
       grind)
    | exact resolve eq500921 eq222133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222133 eq500921
  have eq500957 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq500950 y
       have i₂ := eq498703
       grind)
    | exact superpose eq498703 eq500950
    | exact resolve eq500950 eq498703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500950
  have eq500967 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq500957
       have r₂ := eq499111
       grind)
    | exact resolve eq500957 eq499111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499111 eq500957
  have eq500973 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq500675
       have i₂ := eq500967
       grind)
    | exact superpose eq500967 eq500675
    | exact resolve eq500675 eq500967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500967
  have eq501030 : (M.op x x) = (M.op y y) ∨ (τ (M.op x x)) = (τ x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq500973
  have eq501043 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (τ (M.op x x)) = (τ x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq500358
       have i₂ := eq501030
       grind)
    | exact superpose eq501030 eq500358
    | (have r₁ := eq500358
       have r₂ := eq501030
       grind)
    | exact resolve eq500358 eq501030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500358 eq501030
  have eq501069 : (M.op x y) = (M.op x x) ∨ (τ (M.op x x)) = (τ x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq501043
  have eq501078 : (M.op x y) = (M.op x x) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq501069
       have r₂ := eq500830
       grind)
    | exact resolve eq501069 eq500830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500830 eq501069
  have eq501085 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x x) = (M.op y y) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq500675
       have i₂ := eq501078
       grind)
    | exact superpose eq501078 eq500675
    | exact resolve eq500675 eq501078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500675 eq501078
  have eq501142 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq501085
  have eq501143 : (M.op x x) = (M.op y y) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq501142
  have eq501475 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y y)) ∨ (σ (M.op x x)) = (σ (k y y)) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq239262 y y
       have i₂ := eq501143
       grind)
    | exact superpose eq501143 eq239262
    | (have j0 := eq239262 x x
       grind)
    | exact resolve eq239262 eq501143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239262
  have eq501482 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (k y y) ∨ (σ (M.op x x)) = (σ (k y y)) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq450345 y y
       have i₂ := eq501143
       grind)
    | exact superpose eq501143 eq450345
    | (have j0 := eq450345 x x
       grind)
    | exact resolve eq450345 eq501143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450345
  have eq501499 : y = (k y y) ∨ (σ (M.op x x)) = (σ (k y y)) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq501482
  have eq501501 : (σ y) = (σ (k y y)) ∨ (σ (M.op x x)) = (σ (k y y)) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq501475
  have eq501555 : y = (M.op y y) ∨ (σ (M.op x x)) = (σ (k y y)) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq501499
       have i₂ := eq73 y
       grind)
    | exact superpose eq73 eq501499
    | exact resolve eq501499 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501499
  have eq501562 : (σ y) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k y y)) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq501501
       have i₂ := eq73 y
       grind)
    | exact superpose eq73 eq501501
    | exact resolve eq501501 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501501
  have eq501595 : (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq501555
       have i₂ := eq73 y
       grind)
    | exact superpose eq73 eq501555
    | exact resolve eq501555 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501555
  have eq501596 : y = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (τ (M.op x x)) = (τ x) := by grind
  clear eq501595
  have eq501601 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq501562
       have i₂ := eq73 y
       grind)
    | exact superpose eq73 eq501562
    | exact resolve eq501562 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501562
  have eq501602 : (σ y) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (τ (M.op x x)) = (τ x) := by grind
  clear eq501601
  have eq501661 : y = (M.op x x) ∨ (τ (M.op x x)) = (τ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq501143
       have i₂ := eq501596
       grind)
    | exact superpose eq501596 eq501143
    | exact resolve eq501143 eq501596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501143 eq501596
  have eq502470 : y = (M.op x x) ∨ (τ (M.op x x)) = (τ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq501661
  have eq503267 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (τ (M.op x x)) = (τ x) := by grind
  clear eq501602
  have eq503303 : y = (M.op x x) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq502470
       have r₂ := eq503267
       grind)
    | exact resolve eq502470 eq503267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502470
  have eq503744 : (σ y) ≠ (σ y) ∨ (τ x) = (τ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq472254 x x
       have i₂ := eq503303
       grind)
    | exact superpose eq503303 eq472254
    | (have j0 := eq472254 x x
       grind)
    | exact resolve eq472254 eq503303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472254 eq503303
  have eq503749 : (τ x) = (τ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq503744
  have eq503768 : (τ (M.op x x)) = (τ x) ∨ (σ y) = (σ (k x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq503749
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq503749
    | exact resolve eq503749 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503749
  have eq503769 : (τ (M.op x x)) = (τ x) ∨ (σ y) = (σ (k x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq503768
  have eq503825 : (σ y) = (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq503769
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq503769
    | exact resolve eq503769 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq503769
  have eq503854 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have r₁ := eq503825
       have r₂ := eq503267
       grind)
    | exact resolve eq503825 eq503267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503267 eq503825
  have eq503901 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ (τ (M.op x x)) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq101 X0 y
       have i₂ := eq503854
       grind)
    | exact superpose eq503854 eq101
    | (have j0 := eq101 X0 x
       grind)
    | (have r₁ := eq101 x y
       have r₂ := eq503854
       grind)
    | (have r₁ := eq101 y x
       have r₂ := eq503854
       grind)
    | exact resolve eq101 eq503854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq504144 : (M.op y y) = (τ (σ (M.op x x))) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq503854
       grind)
    | exact superpose eq503854 eq9
    | exact resolve eq9 eq503854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503854
  have eq504203 : (M.op x x) = (M.op y y) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq504144
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq504144
    | exact resolve eq504144 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504144
  have eq504374 : (M.op x x) ≠ (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq128801
       have i₂ := eq504203
       grind)
    | exact superpose eq504203 eq128801
    | (have r₁ := eq128801
       have r₂ := eq504203
       grind)
    | exact resolve eq128801 eq504203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128801
  have eq504434 : (M.op x x) ≠ (M.op x x) ∨ (τ (M.op x x)) = (τ (M.op x y)) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq497156
       have i₂ := eq504203
       grind)
    | exact superpose eq504203 eq497156
    | (have r₁ := eq497156
       have r₂ := eq504203
       grind)
    | exact resolve eq497156 eq504203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497156 eq504203
  have eq505292 : (τ (M.op x x)) = (τ (M.op x y)) ∨ (τ (M.op x x)) = (τ x) := by grind
  clear eq504434
  have eq505352 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) := by grind
  clear eq504374
  have eq505548 : (τ (M.op x x)) = (τ x) ∨ (τ (M.op x x)) = (τ x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq505292
       have i₂ := eq505352
       grind)
    | exact superpose eq505352 eq505292
    | exact resolve eq505292 eq505352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505292 eq505352
  have eq505587 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) := by grind
  clear eq505548
  have eq514234 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have j0 := eq503901 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503901
  have eq514240 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq514234
       have i₂ := eq498703
       grind)
    | exact superpose eq498703 eq514234
    | exact resolve eq514234 eq498703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514234
  have eq514260 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq514240
       grind)
    | exact superpose eq514240 eq16
    | exact resolve eq16 eq514240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514240
  have eq514369 : (τ (M.op x x)) = (τ x) := by
    first
    | (have r₁ := eq514260
       have r₂ := eq505587
       grind)
    | exact resolve eq514260 eq505587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505587 eq514260
  have eq515234 : (M.op x x) = (σ (τ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq514369
       grind)
    | exact superpose eq514369 eq10
    | exact resolve eq10 eq514369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514369
  have eq515913 : x = (M.op x x) := by
    first
    | (have i₁ := eq515234
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq515234
    | exact resolve eq515234 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515234
  have eq516433 : x = (k y x) := by
    first
    | (have i₁ := eq498703
       have i₂ := eq515913
       grind)
    | exact superpose eq515913 eq498703
    | exact resolve eq498703 eq515913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498703
  have eq516446 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq499702
       have i₂ := eq515913
       grind)
    | exact superpose eq515913 eq499702
    | exact resolve eq499702 eq515913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499702
  have eq518045 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq516446
       have i₂ := eq515913
       grind)
    | exact superpose eq515913 eq516446
    | exact resolve eq516446 eq515913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516446
  have eq518046 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq518045
  have eq518394 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq518046
       grind)
    | exact superpose eq518046 eq16
    | exact resolve eq16 eq518046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518046
  have eq518545 : (σ x) ≠ (σ x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq518394
       have i₂ := eq17 y x
       grind)
    | exact superpose eq17 eq518394
    | (have j1 := eq17 y x
       grind)
    | exact resolve eq518394 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq518546 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq518545
  have eq518547 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq518546
       have i₂ := eq515913
       grind)
    | exact superpose eq515913 eq518546
    | exact resolve eq518546 eq515913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515913 eq518546
  have eq518548 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq518547
       have i₂ := eq516433
       grind)
    | exact superpose eq516433 eq518547
    | exact resolve eq518547 eq516433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516433 eq518547
  have eq518549 : x = (M.op x y) := by grind
  clear eq518548
  have eq518593 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq518394
       have i₂ := eq518549
       grind)
    | exact superpose eq518549 eq518394
    | exact resolve eq518394 eq518549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518394 eq518549
  have eq518594 : False := by grind
  exact eq518594
