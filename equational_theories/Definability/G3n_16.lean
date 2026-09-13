import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,Y) else if X = Y then m(Y,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_pxx_y_x_y_pxy_pxy_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : ∀ X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq20
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
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq35
    | exact resolve eq35 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq78 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq75
    | exact resolve eq75 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
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
  have eq98 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq99 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq98
    | exact resolve eq98 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq102 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq99
  have eq691 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq699 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq708 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq699
  have eq716 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq691 X0 X1
       have i₂ := eq80 X1
       grind)
    | exact superpose eq80 eq691
    | (have j0 := eq691 X0 X1
       grind)
    | exact resolve eq691 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq730 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq716
    | (have j0 := eq716 X0 X1
       grind)
    | exact resolve eq716 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq737 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq743 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq753 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq743 (σ X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq743
    | exact resolve eq743 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq753 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq753
    | exact resolve eq753 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq784 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq774 X0
       have i₂ := eq743 X0
       grind)
    | exact superpose eq743 eq774
    | exact resolve eq774 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq774
  have eq890 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq730 x y
       grind)
    | exact superpose eq730 eq16
    | (have j1 := eq730 x y
       grind)
    | exact resolve eq16 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq10376 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq708
    | (have j0 := eq708 X1 (σ X0)
       grind)
    | exact resolve eq708 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq10514 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10376 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10376
    | (have j0 := eq10376 X0 X1
       grind)
    | exact resolve eq10376 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10376
  have eq10527 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10514 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq10514
    | (have j0 := eq10514 X0 X1
       grind)
    | exact resolve eq10514 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10514
  have eq10535 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10527 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq10527
    | (have j0 := eq10527 X0 X1
       grind)
    | exact resolve eq10527 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10527
  have eq16862 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq890
       have i₂ := eq10535 y x
       grind)
    | exact superpose eq10535 eq890
    | (have j1 := eq10535 y x
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 y x
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq890 eq10535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq10535
  have eq16863 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by grind
  clear eq16862
  have eq1774130 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16863
       grind)
    | exact superpose eq16863 eq16
    | exact resolve eq16 eq16863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16863
  have eq1774149 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1774130
       have r₂ := eq80 x
       grind)
    | exact resolve eq1774130 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774130
  have eq1774227 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq784 x
       have i₂ := eq1774149
       grind)
    | exact superpose eq1774149 eq784
    | exact resolve eq784 eq1774149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774149
  have eq1774387 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1774227
       have r₂ := eq16
       grind)
    | exact resolve eq1774227 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774227
  have eq1774460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq102 y
       have i₂ := eq1774387
       grind)
    | exact superpose eq1774387 eq102
    | exact resolve eq102 eq1774387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774387
  have eq1774637 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1774460
       have r₂ := eq16
       grind)
    | exact resolve eq1774460 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774460
  have eq1774655 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq1774637
       grind)
    | exact superpose eq1774637 eq9
    | exact resolve eq9 eq1774637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774637
  have eq1775197 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1774655
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1774655
    | exact resolve eq1774655 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774655
  have eq1775200 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1775197
       grind)
    | exact superpose eq1775197 eq16
    | exact resolve eq16 eq1775197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775197
  have eq1775219 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1775200
       have r₂ := eq80 x
       grind)
    | exact resolve eq1775200 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1775200
  have eq1775440 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1775219
       grind)
    | exact superpose eq1775219 eq9
    | exact resolve eq9 eq1775219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775219
  have eq1776063 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1775440
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1775440
    | exact resolve eq1775440 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775440
  have eq1776155 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq784 x
       have i₂ := eq1776063
       grind)
    | exact superpose eq1776063 eq784
    | exact resolve eq784 eq1776063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq1776063
  have eq1776313 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1776155
       have r₂ := eq16
       grind)
    | exact resolve eq1776155 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776155
  have eq1776544 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1776313
       grind)
    | exact superpose eq1776313 eq9
    | exact resolve eq9 eq1776313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776313
  have eq1777167 : x = (M.op y y) := by
    first
    | (have i₁ := eq1776544
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1776544
    | exact resolve eq1776544 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776544
  have eq1777394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102 y
       have i₂ := eq1777167
       grind)
    | exact superpose eq1777167 eq102
    | exact resolve eq102 eq1777167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq1777167
  have eq1777569 : False := by grind
  exact eq1777569

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(Y,X) else if X = Y then m(X,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_pxx_y_x_y_pyx_pyx_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : ∀ X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq20
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
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq35
    | exact resolve eq35 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq78 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq75
    | exact resolve eq75 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
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
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq99 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq98
    | exact resolve eq98 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq99
  have eq691 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq699 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq708 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq699
  have eq716 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq691 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq691
    | (have j0 := eq691 X0 X1
       grind)
    | exact resolve eq691 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq730 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 X1
       have i₂ := eq80 X1
       grind)
    | exact superpose eq80 eq716
    | (have j0 := eq716 X0 X1
       grind)
    | exact resolve eq716 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq737 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq743 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq753 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq743 (σ X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq743
    | exact resolve eq743 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq753 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq753
    | exact resolve eq753 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq784 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq774 X0
       have i₂ := eq743 X0
       grind)
    | exact superpose eq743 eq774
    | exact resolve eq774 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq774
  have eq890 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq730 x y
       grind)
    | exact superpose eq730 eq16
    | (have j1 := eq730 x y
       grind)
    | exact resolve eq16 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq10376 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq708 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq708
    | (have j0 := eq708 (σ X0) X1
       grind)
    | exact resolve eq708 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq10514 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10376 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10376
    | (have j0 := eq10376 X0 X1
       grind)
    | exact resolve eq10376 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10376
  have eq10527 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10514 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq10514
    | (have j0 := eq10514 X0 X1
       grind)
    | exact resolve eq10514 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10514
  have eq10535 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10527 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq10527
    | (have j0 := eq10527 X0 X1
       grind)
    | exact resolve eq10527 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10527
  have eq16862 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq890
       have i₂ := eq10535 x y
       grind)
    | exact superpose eq10535 eq890
    | (have j1 := eq10535 x y
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 x y
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq890 eq10535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq10535
  have eq16863 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by grind
  clear eq16862
  have eq1774135 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16863
       grind)
    | exact superpose eq16863 eq16
    | exact resolve eq16 eq16863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16863
  have eq1774154 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1774135
       have r₂ := eq80 x
       grind)
    | exact resolve eq1774135 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774135
  have eq1774214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq102 x
       have i₂ := eq1774154
       grind)
    | exact superpose eq1774154 eq102
    | exact resolve eq102 eq1774154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774154
  have eq1774392 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1774214
       have r₂ := eq16
       grind)
    | exact resolve eq1774214 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774214
  have eq1774482 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq784 y
       have i₂ := eq1774392
       grind)
    | exact superpose eq1774392 eq784
    | exact resolve eq784 eq1774392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774392
  have eq1774641 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1774482
       have r₂ := eq16
       grind)
    | exact resolve eq1774482 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774482
  have eq1774660 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq1774641
       grind)
    | exact superpose eq1774641 eq9
    | exact resolve eq9 eq1774641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774641
  have eq1775202 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1774660
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1774660
    | exact resolve eq1774660 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774660
  have eq1775205 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1775202
       grind)
    | exact superpose eq1775202 eq16
    | exact resolve eq16 eq1775202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775202
  have eq1775224 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1775205
       have r₂ := eq80 x
       grind)
    | exact resolve eq1775205 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1775205
  have eq1775445 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1775224
       grind)
    | exact superpose eq1775224 eq9
    | exact resolve eq9 eq1775224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775224
  have eq1776068 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1775445
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1775445
    | exact resolve eq1775445 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775445
  have eq1776142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq102 x
       have i₂ := eq1776068
       grind)
    | exact superpose eq1776068 eq102
    | exact resolve eq102 eq1776068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq1776068
  have eq1776318 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1776142
       have r₂ := eq16
       grind)
    | exact resolve eq1776142 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776142
  have eq1776548 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1776318
       grind)
    | exact superpose eq1776318 eq9
    | exact resolve eq9 eq1776318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776318
  have eq1777171 : x = (M.op y y) := by
    first
    | (have i₁ := eq1776548
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1776548
    | exact resolve eq1776548 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776548
  have eq1777416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq784 y
       have i₂ := eq1777171
       grind)
    | exact superpose eq1777171 eq784
    | exact resolve eq784 eq1777171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq1777171
  have eq1777573 : False := by grind
  exact eq1777573

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(Y,X) else if X = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_pxx_y_x_y_pyx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : ∀ X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq20
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
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq35
    | exact resolve eq35 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq78 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq75
    | exact resolve eq75 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
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
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq99 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq98
    | exact resolve eq98 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq99
  have eq691 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq699 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq708 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq699
  have eq716 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq691 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq691
    | (have j0 := eq691 X0 X1
       grind)
    | exact resolve eq691 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq730 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 X1
       have i₂ := eq80 X1
       grind)
    | exact superpose eq80 eq716
    | (have j0 := eq716 X0 X1
       grind)
    | exact resolve eq716 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq737 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq743 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq753 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq743 (σ X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq743
    | exact resolve eq743 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq753 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq753
    | exact resolve eq753 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq784 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq774 X0
       have i₂ := eq743 X0
       grind)
    | exact superpose eq743 eq774
    | exact resolve eq774 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq774
  have eq890 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq730 x y
       grind)
    | exact superpose eq730 eq16
    | (have j1 := eq730 x y
       grind)
    | exact resolve eq16 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq10376 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq708 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq708
    | (have j0 := eq708 (σ X0) X1
       grind)
    | exact resolve eq708 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq10514 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10376 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10376
    | (have j0 := eq10376 X0 X1
       grind)
    | exact resolve eq10376 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10376
  have eq10527 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10514 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq10514
    | (have j0 := eq10514 X0 X1
       grind)
    | exact resolve eq10514 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10514
  have eq10535 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10527 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq10527
    | (have j0 := eq10527 X0 X1
       grind)
    | exact resolve eq10527 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10527
  have eq16862 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq890
       have i₂ := eq10535 x y
       grind)
    | exact superpose eq10535 eq890
    | (have j1 := eq10535 x y
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 x y
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq890 eq10535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq10535
  have eq16863 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by grind
  clear eq16862
  have eq1774135 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16863
       grind)
    | exact superpose eq16863 eq16
    | exact resolve eq16 eq16863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16863
  have eq1774154 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1774135
       have r₂ := eq80 x
       grind)
    | exact resolve eq1774135 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774135
  have eq1774214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq102 x
       have i₂ := eq1774154
       grind)
    | exact superpose eq1774154 eq102
    | exact resolve eq102 eq1774154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774154
  have eq1774392 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1774214
       have r₂ := eq16
       grind)
    | exact resolve eq1774214 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774214
  have eq1774482 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq784 y
       have i₂ := eq1774392
       grind)
    | exact superpose eq1774392 eq784
    | exact resolve eq784 eq1774392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774392
  have eq1774641 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1774482
       have r₂ := eq16
       grind)
    | exact resolve eq1774482 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774482
  have eq1774660 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq1774641
       grind)
    | exact superpose eq1774641 eq9
    | exact resolve eq9 eq1774641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774641
  have eq1775202 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1774660
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1774660
    | exact resolve eq1774660 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774660
  have eq1775205 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1775202
       grind)
    | exact superpose eq1775202 eq16
    | exact resolve eq16 eq1775202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775202
  have eq1775224 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1775205
       have r₂ := eq80 x
       grind)
    | exact resolve eq1775205 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1775205
  have eq1775445 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1775224
       grind)
    | exact superpose eq1775224 eq9
    | exact resolve eq9 eq1775224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775224
  have eq1776068 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1775445
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1775445
    | exact resolve eq1775445 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775445
  have eq1776142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq102 x
       have i₂ := eq1776068
       grind)
    | exact superpose eq1776068 eq102
    | exact resolve eq102 eq1776068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq1776068
  have eq1776318 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1776142
       have r₂ := eq16
       grind)
    | exact resolve eq1776142 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776142
  have eq1776548 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1776318
       grind)
    | exact superpose eq1776318 eq9
    | exact resolve eq9 eq1776318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776318
  have eq1777171 : x = (M.op y y) := by
    first
    | (have i₁ := eq1776548
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1776548
    | exact resolve eq1776548 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776548
  have eq1777416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq784 y
       have i₂ := eq1777171
       grind)
    | exact superpose eq1777171 eq784
    | exact resolve eq784 eq1777171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq1777171
  have eq1777573 : False := by grind
  exact eq1777573

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(Y,X) else if X = Y then m(Y,Y)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_pxx_y_x_y_pyx_pyx_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : ∀ X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq20
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
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq35
    | exact resolve eq35 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq78 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq75
    | exact resolve eq75 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
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
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq99 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq98
    | exact resolve eq98 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq99
  have eq691 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq699 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq708 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq699
  have eq716 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq691 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq691
    | (have j0 := eq691 X0 X1
       grind)
    | exact resolve eq691 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq730 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 X1
       have i₂ := eq80 X1
       grind)
    | exact superpose eq80 eq716
    | (have j0 := eq716 X0 X1
       grind)
    | exact resolve eq716 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq737 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq743 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq753 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq743 (σ X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq743
    | exact resolve eq743 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq753 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq753
    | exact resolve eq753 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq784 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq774 X0
       have i₂ := eq743 X0
       grind)
    | exact superpose eq743 eq774
    | exact resolve eq774 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq774
  have eq890 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq730 x y
       grind)
    | exact superpose eq730 eq16
    | (have j1 := eq730 x y
       grind)
    | exact resolve eq16 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq10376 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq708 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq708
    | (have j0 := eq708 (σ X0) X1
       grind)
    | exact resolve eq708 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq10514 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10376 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10376
    | (have j0 := eq10376 X0 X1
       grind)
    | exact resolve eq10376 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10376
  have eq10527 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10514 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq10514
    | (have j0 := eq10514 X0 X1
       grind)
    | exact resolve eq10514 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10514
  have eq10535 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10527 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq10527
    | (have j0 := eq10527 X0 X1
       grind)
    | exact resolve eq10527 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10527
  have eq16862 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq890
       have i₂ := eq10535 x y
       grind)
    | exact superpose eq10535 eq890
    | (have j1 := eq10535 x y
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 x y
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq890 eq10535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq10535
  have eq16863 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by grind
  clear eq16862
  have eq1774135 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16863
       grind)
    | exact superpose eq16863 eq16
    | exact resolve eq16 eq16863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16863
  have eq1774154 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1774135
       have r₂ := eq80 x
       grind)
    | exact resolve eq1774135 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774135
  have eq1774214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq102 x
       have i₂ := eq1774154
       grind)
    | exact superpose eq1774154 eq102
    | exact resolve eq102 eq1774154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774154
  have eq1774392 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1774214
       have r₂ := eq16
       grind)
    | exact resolve eq1774214 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774214
  have eq1774482 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq784 y
       have i₂ := eq1774392
       grind)
    | exact superpose eq1774392 eq784
    | exact resolve eq784 eq1774392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774392
  have eq1774641 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1774482
       have r₂ := eq16
       grind)
    | exact resolve eq1774482 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774482
  have eq1774660 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq1774641
       grind)
    | exact superpose eq1774641 eq9
    | exact resolve eq9 eq1774641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774641
  have eq1775202 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1774660
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1774660
    | exact resolve eq1774660 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774660
  have eq1775205 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1775202
       grind)
    | exact superpose eq1775202 eq16
    | exact resolve eq16 eq1775202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775202
  have eq1775224 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1775205
       have r₂ := eq80 x
       grind)
    | exact resolve eq1775205 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1775205
  have eq1775445 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1775224
       grind)
    | exact superpose eq1775224 eq9
    | exact resolve eq9 eq1775224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775224
  have eq1776068 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1775445
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1775445
    | exact resolve eq1775445 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775445
  have eq1776142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq102 x
       have i₂ := eq1776068
       grind)
    | exact superpose eq1776068 eq102
    | exact resolve eq102 eq1776068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq1776068
  have eq1776318 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1776142
       have r₂ := eq16
       grind)
    | exact resolve eq1776142 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776142
  have eq1776548 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1776318
       grind)
    | exact superpose eq1776318 eq9
    | exact resolve eq9 eq1776318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776318
  have eq1777171 : x = (M.op y y) := by
    first
    | (have i₁ := eq1776548
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1776548
    | exact resolve eq1776548 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776548
  have eq1777416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq784 y
       have i₂ := eq1777171
       grind)
    | exact superpose eq1777171 eq784
    | exact resolve eq784 eq1777171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq1777171
  have eq1777573 : False := by grind
  exact eq1777573

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else if m(X,X) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_x_y_pxx_y_pyx_pxx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : (M.op x y) = (M.op x y) := by grind
  have eq21 : (M.op x y) = (M.op x y) := by grind
  clear eq20
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq23 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq22
  have eq24 : (σ x) = (σ x) := by grind
  have eq25 : (σ x) = (σ x) := by grind
  clear eq24
  have eq26 : (σ y) = (σ y) := by grind
  have eq27 : (σ y) = (σ y) := by grind
  clear eq26
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq29 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq28
  have eq30 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq31 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq46 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq52 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq64 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  have eq65 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq52
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq39
    | (have j0 := eq39 x
       grind)
    | exact resolve eq39 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq39
    | (have j0 := eq39 y
       grind)
    | exact resolve eq39 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq47
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq47
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq47 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq86
    | exact resolve eq86 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq94 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq108 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq99
  have eq257 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq387 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq388 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq389 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq387 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq387
    | (have j0 := eq387 X0
       grind)
    | exact resolve eq387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq2917 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq388 (τ X0)
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq388
    | (have j0 := eq388 (τ X0)
       grind)
    | exact resolve eq388 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2924 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2917 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2917
    | (have j0 := eq2917 X0
       grind)
    | exact resolve eq2917 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2917
  have eq2930 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2924 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2924
    | (have j0 := eq2924 X0
       grind)
    | exact resolve eq2924 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2924
  have eq3167 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq389 (τ X0)
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq389
    | (have j0 := eq389 (τ X0)
       grind)
    | exact resolve eq389 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq3177 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3167 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3167
    | (have j0 := eq3167 X0
       grind)
    | exact resolve eq3167 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167
  have eq3192 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3177 X0
       have i₂ := eq41 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq41 eq3177
    | (have j0 := eq3177 X0
       grind)
    | exact resolve eq3177 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq3177
  have eq3205 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3192 X0
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq3192
    | (have j0 := eq3192 X0
       grind)
    | exact resolve eq3192 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3192
  have eq3212 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3205 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3205
    | (have j0 := eq3205 X0
       grind)
    | exact resolve eq3205 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205
  have eq3219 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3212 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3212
    | (have j0 := eq3212 X0
       grind)
    | exact resolve eq3212 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3212
  have eq5724 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq257 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq257
    | exact resolve eq257 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq5822 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (k X0 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5724 X0
       have i₂ := eq10 X0 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5724
    | (have j0 := eq5724 X0
       grind)
    | exact resolve eq5724 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5724
  have eq15382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq15383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15382
    | exact resolve eq15382 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15382
  have eq15394 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq15383
       have r₂ := eq30
       grind)
    | exact resolve eq15383 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15383
  have eq15396 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15394 eq65
    | exact resolve eq65 eq15394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq15394
  have eq15400 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq15396
  have eq15402 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq15400
    | exact resolve eq15400 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15400
  have eq15603 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15402 eq108
    | exact resolve eq108 eq15402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq15402
  have eq15607 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq15603
  have eq15609 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq15607
    | exact resolve eq15607 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15607
  have eq15623 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  have eq15631 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15623
  have eq15660 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq15631
       grind)
    | exact superpose eq15631 eq64
    | exact resolve eq64 eq15631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15662 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15631
  have eq15665 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq15660
  have eq15666 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15662
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq15662
    | exact resolve eq15662 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15662
  have eq15667 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15665
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq15665
    | exact resolve eq15665 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15665
  have eq15867 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq15666
       grind)
    | exact superpose eq15666 eq72
    | exact resolve eq72 eq15666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15666
  have eq15887 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq15867
    | exact resolve eq15867 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15867
  have eq15906 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15667 eq3219
    | (have j0 := eq3219 (σ x)
       grind)
    | exact resolve eq3219 eq15667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3219
  have eq15908 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15906
    | exact resolve eq15906 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15906
  have eq70957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15908 eq15887
    | exact resolve eq15887 eq15908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15887 eq15908
  have eq70960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq70957
  have eq70969 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq70960
       have r₂ := eq30
       grind)
    | exact resolve eq70960 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70960
  have eq70975 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq71001 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq70975 eq15667
    | exact resolve eq15667 eq70975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15667 eq70975
  have eq71020 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq71001
  have eq71037 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq71020 eq70969
    | exact resolve eq70969 eq71020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70969 eq71020
  have eq71043 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq71037
  have eq71061 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq71069 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq71061
  have eq71839 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq71069
  have eq72615 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71043
       have i₂ := eq71839
       grind)
    | exact superpose eq71839 eq71043
    | exact resolve eq71043 eq71839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71043 eq71839
  have eq72622 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72615
  have eq72634 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq72622
       grind)
    | exact superpose eq72622 eq94
    | exact resolve eq94 eq72622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72635 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72622
  have eq72637 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq72635
  have eq72638 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq72634
  have eq72640 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72637
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq72637
    | exact resolve eq72637 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72637
  have eq72641 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72638
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq72638
    | exact resolve eq72638 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72638
  have eq73261 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq77014 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq72640
       grind)
    | exact superpose eq72640 eq72
    | exact resolve eq72 eq72640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72640
  have eq77057 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq77014
    | exact resolve eq77014 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77014
  have eq77062 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq73261
  have eq105322 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq77062 eq72641
    | exact resolve eq72641 eq77062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72641 eq77062
  have eq105373 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq105322
  have eq106104 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq105373
  have eq106106 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq106104
  have eq106109 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq106106
    | exact resolve eq106106 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106106
  have eq106510 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq106109 eq77057
    | exact resolve eq77057 eq106109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq106510
  have eq106524 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq106513
       have r₂ := eq30
       grind)
    | exact resolve eq106513 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106513
  have eq106530 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq106524
  have eq106535 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq106530
    | exact resolve eq106530 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106530
  have eq106557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq106535 eq77057
    | exact resolve eq77057 eq106535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77057 eq106535
  have eq106560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq106557
  have eq106571 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq106560
       have r₂ := eq30
       grind)
    | exact resolve eq106560 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106560
  have eq106577 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq106571
  have eq106583 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq106577
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq106577
    | exact resolve eq106577 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106577
  have eq107468 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq106583
       grind)
    | exact superpose eq106583 eq72
    | exact resolve eq72 eq106583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106583
  have eq107511 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq107468
    | exact resolve eq107468 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107468
  have eq108450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq107511 eq106109
    | exact resolve eq106109 eq107511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106109
  have eq108455 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq108450
  have eq108473 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq108455
       have r₂ := eq30
       grind)
    | exact resolve eq108455 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108455
  have eq108548 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq108473
  have eq108553 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq108548
    | exact resolve eq108548 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108548
  have eq109315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq108553 eq107511
    | exact resolve eq107511 eq108553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107511 eq108553
  have eq109318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq109315
  have eq109331 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq109318
       have r₂ := eq30
       grind)
    | exact resolve eq109318 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109318
  have eq109335 : (k x x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq110047 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46
       have i₂ := eq109335
       grind)
    | exact superpose eq109335 eq46
    | exact resolve eq46 eq109335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq110063 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15609
       have i₂ := eq109335
       grind)
    | exact superpose eq109335 eq15609
    | exact resolve eq15609 eq109335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15609 eq109335
  have eq110100 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq110063
  have eq110114 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq110047
       have i₂ := eq109331
       grind)
    | exact superpose eq109331 eq110047
    | exact resolve eq110047 eq109331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110047
  have eq110237 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq110114
  have eq110243 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq110237
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq110237
    | exact resolve eq110237 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110237
  have eq110280 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq110243 eq2930
    | (have j0 := eq2930 (σ x)
       grind)
    | (have r₁ := eq2930 (σ x)
       have r₂ := eq110243
       grind)
    | exact resolve eq2930 eq110243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2930 eq110243
  have eq110287 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq110280
  have eq2064207 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq109331
       have i₂ := eq110100
       grind)
    | exact superpose eq110100 eq109331
    | exact resolve eq109331 eq110100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110100
  have eq2065531 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2064207
  have eq2066199 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  have eq2066212 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2066199
  have eq2068277 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2066212
  have eq2070441 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2065531
       have i₂ := eq2068277
       grind)
    | exact superpose eq2068277 eq2065531
    | exact resolve eq2065531 eq2068277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065531 eq2068277
  have eq2070452 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2070441
  have eq2070507 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq2070452
       grind)
    | exact superpose eq2070452 eq94
    | exact resolve eq94 eq2070452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq2070516 : (σ (M.op x y)) = (σ (k y x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5822 y
       have i₂ := eq2070452
       grind)
    | exact superpose eq2070452 eq5822
    | exact resolve eq5822 eq2070452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5822 eq2070452
  have eq2070524 : (σ (M.op x y)) = (σ (k y x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq2070516
  have eq2070533 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2070507
  have eq2070539 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2070524
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq2070524
    | exact resolve eq2070524 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq2070524
  have eq2070546 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2070533
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2070533
    | exact resolve eq2070533 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070533
  have eq2070549 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2070539
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq2070539
    | exact resolve eq2070539 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070539
  have eq2070553 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23 eq2070549
    | exact resolve eq2070549 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070549
  have eq2072680 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq2092990 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2072680
  have eq2260984 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2092990 eq2070546
    | exact resolve eq2070546 eq2092990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070546 eq2092990
  have eq2261107 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2260984
  have eq2261164 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2261107
  have eq2261166 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq2261164
  have eq2261175 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq29 eq2261166
    | exact resolve eq2261166 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261166
  have eq2262311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2261175 eq2070553
    | exact resolve eq2070553 eq2261175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070553 eq2261175
  have eq2262316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2262311
  have eq2262333 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2262316
       have r₂ := eq30
       grind)
    | exact resolve eq2262316 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262316
  have eq2262345 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2262333 eq110287
    | exact resolve eq110287 eq2262333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110287 eq2262333
  have eq2263605 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2262345
  have eq2264097 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109331
       have i₂ := eq2263605
       grind)
    | exact superpose eq2263605 eq109331
    | exact resolve eq109331 eq2263605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109331 eq2263605
  have eq2265427 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2264097
  have eq2266014 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2265427 eq32
    | exact resolve eq32 eq2265427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2265427
  have eq2266485 : x = y ∨ x = y := by
    first
    | exact superpose eq31 eq2266014
    | exact resolve eq2266014 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2266014
  have eq2266486 : x = y := by grind
  clear eq2266485
  have eq2266493 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq21
       have i₂ := eq2266486
       grind)
    | exact superpose eq2266486 eq21
    | exact resolve eq21 eq2266486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2266494 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27
       have i₂ := eq2266486
       grind)
    | exact superpose eq2266486 eq27
    | exact resolve eq27 eq2266486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2266486
  have eq2267678 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2266494
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2266494
    | exact resolve eq2266494 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266494
  have eq2267684 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2267678 eq29
    | exact resolve eq29 eq2267678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2267678
  have eq2268224 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq2266493
       grind)
    | exact superpose eq2266493 eq64
    | exact resolve eq64 eq2266493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq2268910 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  have eq2268923 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23 eq2268224
    | exact resolve eq2268224 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268224
  have eq2269592 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  have eq2274435 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq2274454 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2267684 eq2274435
    | exact resolve eq2274435 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274435
  have eq2274502 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2274454
       have r₂ := eq30
       grind)
    | exact resolve eq2274454 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274454
  have eq2274527 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2267684 eq2274502
    | exact resolve eq2274502 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274502
  have eq2274553 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2274527 eq2269592
    | exact resolve eq2269592 eq2274527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269592 eq2274527
  have eq2274555 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2267684 eq2274553
    | exact resolve eq2274553 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274553
  have eq2276287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2274555 eq2268923
    | exact resolve eq2268923 eq2274555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268923 eq2274555
  have eq2276305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2276287
  have eq2276312 : x = (M.op x y) := by
    first
    | (have r₁ := eq2276305
       have r₂ := eq30
       grind)
    | exact resolve eq2276305 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276305
  have eq2276366 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2276312 eq23
    | exact resolve eq23 eq2276312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq2277235 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq2276312 eq2268910
    | exact resolve eq2268910 eq2276312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268910
  have eq2277238 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq2277235
       have i₂ := eq2266493
       grind)
    | exact superpose eq2266493 eq2277235
    | exact resolve eq2277235 eq2266493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266493 eq2277235
  have eq2277818 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2276366
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2276366
    | exact resolve eq2276366 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276366
  have eq2277820 : x = (k x x) := by
    first
    | exact superpose eq2276312 eq2277238
    | exact resolve eq2277238 eq2276312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276312 eq2277238
  have eq2282689 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq388 x
       have i₂ := eq2277820
       grind)
    | exact superpose eq2277820 eq388
    | (have j0 := eq388 x
       grind)
    | exact resolve eq388 eq2277820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq2277820
  have eq2282707 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2282689
  have eq2282724 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2282707
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2282707
    | exact resolve eq2282707 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2282707
  have eq2282816 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2267684 eq2282724
    | exact resolve eq2282724 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267684 eq2282724
  have eq2282903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2277818 eq2282816
    | exact resolve eq2282816 eq2277818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277818 eq2282816
  have eq2282987 : False := by grind
  exact eq2282987

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,Y) else if m(X,X) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_x_y_pxx_y_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : (M.op x y) = (M.op x y) := by grind
  have eq21 : (M.op x y) = (M.op x y) := by grind
  clear eq20
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq23 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq22
  have eq24 : (σ x) = (σ x) := by grind
  have eq25 : (σ x) = (σ x) := by grind
  clear eq24
  have eq26 : (σ y) = (σ y) := by grind
  have eq27 : (σ y) = (σ y) := by grind
  clear eq26
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq29 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq28
  have eq30 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq31 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq46 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq52 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq64 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  have eq65 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq52
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq39
    | (have j0 := eq39 x
       grind)
    | exact resolve eq39 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq39
    | (have j0 := eq39 y
       grind)
    | exact resolve eq39 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq47
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq47
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq47 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq86
    | exact resolve eq86 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq94 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq108 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq99
  have eq257 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq387 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq388 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq389 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq387 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq387
    | (have j0 := eq387 X0
       grind)
    | exact resolve eq387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq2917 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq388 (τ X0)
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq388
    | (have j0 := eq388 (τ X0)
       grind)
    | exact resolve eq388 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2924 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2917 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2917
    | (have j0 := eq2917 X0
       grind)
    | exact resolve eq2917 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2917
  have eq2930 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2924 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2924
    | (have j0 := eq2924 X0
       grind)
    | exact resolve eq2924 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2924
  have eq3167 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq389 (τ X0)
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq389
    | (have j0 := eq389 (τ X0)
       grind)
    | exact resolve eq389 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq3177 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3167 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3167
    | (have j0 := eq3167 X0
       grind)
    | exact resolve eq3167 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167
  have eq3192 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3177 X0
       have i₂ := eq41 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq41 eq3177
    | (have j0 := eq3177 X0
       grind)
    | exact resolve eq3177 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq3177
  have eq3205 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3192 X0
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq3192
    | (have j0 := eq3192 X0
       grind)
    | exact resolve eq3192 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3192
  have eq3212 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3205 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3205
    | (have j0 := eq3205 X0
       grind)
    | exact resolve eq3205 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205
  have eq3219 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3212 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3212
    | (have j0 := eq3212 X0
       grind)
    | exact resolve eq3212 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3212
  have eq5724 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq257 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq257
    | exact resolve eq257 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq5822 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (k X0 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5724 X0
       have i₂ := eq10 X0 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5724
    | (have j0 := eq5724 X0
       grind)
    | exact resolve eq5724 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5724
  have eq15382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq15383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15382
    | exact resolve eq15382 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15382
  have eq15394 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq15383
       have r₂ := eq30
       grind)
    | exact resolve eq15383 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15383
  have eq15396 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15394 eq65
    | exact resolve eq65 eq15394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq15394
  have eq15400 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq15396
  have eq15402 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq15400
    | exact resolve eq15400 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15400
  have eq15603 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15402 eq108
    | exact resolve eq108 eq15402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq15402
  have eq15607 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq15603
  have eq15609 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq15607
    | exact resolve eq15607 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15607
  have eq15623 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  have eq15631 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15623
  have eq15660 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq15631
       grind)
    | exact superpose eq15631 eq64
    | exact resolve eq64 eq15631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15662 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15631
  have eq15665 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq15660
  have eq15666 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15662
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq15662
    | exact resolve eq15662 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15662
  have eq15667 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15665
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq15665
    | exact resolve eq15665 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15665
  have eq15867 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq15666
       grind)
    | exact superpose eq15666 eq72
    | exact resolve eq72 eq15666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15666
  have eq15887 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq15867
    | exact resolve eq15867 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15867
  have eq15906 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15667 eq3219
    | (have j0 := eq3219 (σ x)
       grind)
    | exact resolve eq3219 eq15667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3219
  have eq15908 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15906
    | exact resolve eq15906 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15906
  have eq70957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15908 eq15887
    | exact resolve eq15887 eq15908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15887 eq15908
  have eq70960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq70957
  have eq70969 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq70960
       have r₂ := eq30
       grind)
    | exact resolve eq70960 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70960
  have eq70975 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq71001 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq70975 eq15667
    | exact resolve eq15667 eq70975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15667 eq70975
  have eq71020 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq71001
  have eq71037 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq71020 eq70969
    | exact resolve eq70969 eq71020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70969 eq71020
  have eq71043 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq71037
  have eq71061 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq71069 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq71061
  have eq71839 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq71069
  have eq72615 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71043
       have i₂ := eq71839
       grind)
    | exact superpose eq71839 eq71043
    | exact resolve eq71043 eq71839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71043 eq71839
  have eq72622 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72615
  have eq72634 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq72622
       grind)
    | exact superpose eq72622 eq94
    | exact resolve eq94 eq72622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72635 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72622
  have eq72637 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq72635
  have eq72638 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq72634
  have eq72640 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72637
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq72637
    | exact resolve eq72637 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72637
  have eq72641 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72638
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq72638
    | exact resolve eq72638 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72638
  have eq73261 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq77014 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq72640
       grind)
    | exact superpose eq72640 eq72
    | exact resolve eq72 eq72640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72640
  have eq77057 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq77014
    | exact resolve eq77014 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77014
  have eq77062 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq73261
  have eq105322 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq77062 eq72641
    | exact resolve eq72641 eq77062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72641 eq77062
  have eq105373 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq105322
  have eq106104 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq105373
  have eq106106 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq106104
  have eq106109 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq106106
    | exact resolve eq106106 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106106
  have eq106510 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq106109 eq77057
    | exact resolve eq77057 eq106109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq106510
  have eq106524 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq106513
       have r₂ := eq30
       grind)
    | exact resolve eq106513 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106513
  have eq106530 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq106524
  have eq106535 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq106530
    | exact resolve eq106530 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106530
  have eq106557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq106535 eq77057
    | exact resolve eq77057 eq106535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77057 eq106535
  have eq106560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq106557
  have eq106571 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq106560
       have r₂ := eq30
       grind)
    | exact resolve eq106560 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106560
  have eq106577 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq106571
  have eq106583 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq106577
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq106577
    | exact resolve eq106577 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106577
  have eq107468 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq106583
       grind)
    | exact superpose eq106583 eq72
    | exact resolve eq72 eq106583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106583
  have eq107511 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq107468
    | exact resolve eq107468 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107468
  have eq108450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq107511 eq106109
    | exact resolve eq106109 eq107511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106109
  have eq108455 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq108450
  have eq108473 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq108455
       have r₂ := eq30
       grind)
    | exact resolve eq108455 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108455
  have eq108548 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq108473
  have eq108553 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq108548
    | exact resolve eq108548 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108548
  have eq109315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq108553 eq107511
    | exact resolve eq107511 eq108553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107511 eq108553
  have eq109318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq109315
  have eq109331 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq109318
       have r₂ := eq30
       grind)
    | exact resolve eq109318 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109318
  have eq109335 : (k x x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq110047 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46
       have i₂ := eq109335
       grind)
    | exact superpose eq109335 eq46
    | exact resolve eq46 eq109335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq110063 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15609
       have i₂ := eq109335
       grind)
    | exact superpose eq109335 eq15609
    | exact resolve eq15609 eq109335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15609 eq109335
  have eq110100 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq110063
  have eq110114 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq110047
       have i₂ := eq109331
       grind)
    | exact superpose eq109331 eq110047
    | exact resolve eq110047 eq109331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110047
  have eq110237 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq110114
  have eq110243 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq110237
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq110237
    | exact resolve eq110237 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110237
  have eq110280 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq110243 eq2930
    | (have j0 := eq2930 (σ x)
       grind)
    | (have r₁ := eq2930 (σ x)
       have r₂ := eq110243
       grind)
    | exact resolve eq2930 eq110243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2930 eq110243
  have eq110287 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq110280
  have eq2064207 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq109331
       have i₂ := eq110100
       grind)
    | exact superpose eq110100 eq109331
    | exact resolve eq109331 eq110100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110100
  have eq2065531 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2064207
  have eq2066199 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  have eq2066212 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2066199
  have eq2068277 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2066212
  have eq2070441 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2065531
       have i₂ := eq2068277
       grind)
    | exact superpose eq2068277 eq2065531
    | exact resolve eq2065531 eq2068277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065531 eq2068277
  have eq2070452 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2070441
  have eq2070507 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq2070452
       grind)
    | exact superpose eq2070452 eq94
    | exact resolve eq94 eq2070452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq2070516 : (σ (M.op x y)) = (σ (k y x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5822 y
       have i₂ := eq2070452
       grind)
    | exact superpose eq2070452 eq5822
    | exact resolve eq5822 eq2070452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5822 eq2070452
  have eq2070524 : (σ (M.op x y)) = (σ (k y x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq2070516
  have eq2070533 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2070507
  have eq2070539 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2070524
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq2070524
    | exact resolve eq2070524 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq2070524
  have eq2070546 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2070533
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2070533
    | exact resolve eq2070533 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070533
  have eq2070549 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2070539
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq2070539
    | exact resolve eq2070539 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070539
  have eq2070553 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23 eq2070549
    | exact resolve eq2070549 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070549
  have eq2072680 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq2092990 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2072680
  have eq2260984 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2092990 eq2070546
    | exact resolve eq2070546 eq2092990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070546 eq2092990
  have eq2261107 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2260984
  have eq2261164 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2261107
  have eq2261166 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq2261164
  have eq2261175 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq29 eq2261166
    | exact resolve eq2261166 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261166
  have eq2262311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2261175 eq2070553
    | exact resolve eq2070553 eq2261175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070553 eq2261175
  have eq2262316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2262311
  have eq2262333 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2262316
       have r₂ := eq30
       grind)
    | exact resolve eq2262316 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262316
  have eq2262345 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2262333 eq110287
    | exact resolve eq110287 eq2262333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110287 eq2262333
  have eq2263605 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2262345
  have eq2264097 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109331
       have i₂ := eq2263605
       grind)
    | exact superpose eq2263605 eq109331
    | exact resolve eq109331 eq2263605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109331 eq2263605
  have eq2265427 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2264097
  have eq2266014 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2265427 eq32
    | exact resolve eq32 eq2265427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2265427
  have eq2266485 : x = y ∨ x = y := by
    first
    | exact superpose eq31 eq2266014
    | exact resolve eq2266014 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2266014
  have eq2266486 : x = y := by grind
  clear eq2266485
  have eq2266493 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq21
       have i₂ := eq2266486
       grind)
    | exact superpose eq2266486 eq21
    | exact resolve eq21 eq2266486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2266494 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27
       have i₂ := eq2266486
       grind)
    | exact superpose eq2266486 eq27
    | exact resolve eq27 eq2266486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2266486
  have eq2267678 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2266494
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2266494
    | exact resolve eq2266494 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266494
  have eq2267684 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2267678 eq29
    | exact resolve eq29 eq2267678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2267678
  have eq2268224 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq2266493
       grind)
    | exact superpose eq2266493 eq64
    | exact resolve eq64 eq2266493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq2268910 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  have eq2268923 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23 eq2268224
    | exact resolve eq2268224 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268224
  have eq2269592 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  have eq2274435 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq2274454 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2267684 eq2274435
    | exact resolve eq2274435 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274435
  have eq2274502 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2274454
       have r₂ := eq30
       grind)
    | exact resolve eq2274454 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274454
  have eq2274527 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2267684 eq2274502
    | exact resolve eq2274502 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274502
  have eq2274553 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2274527 eq2269592
    | exact resolve eq2269592 eq2274527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269592 eq2274527
  have eq2274555 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2267684 eq2274553
    | exact resolve eq2274553 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274553
  have eq2276287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2274555 eq2268923
    | exact resolve eq2268923 eq2274555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268923 eq2274555
  have eq2276305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2276287
  have eq2276312 : x = (M.op x y) := by
    first
    | (have r₁ := eq2276305
       have r₂ := eq30
       grind)
    | exact resolve eq2276305 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276305
  have eq2276366 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2276312 eq23
    | exact resolve eq23 eq2276312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq2277235 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq2276312 eq2268910
    | exact resolve eq2268910 eq2276312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268910
  have eq2277238 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq2277235
       have i₂ := eq2266493
       grind)
    | exact superpose eq2266493 eq2277235
    | exact resolve eq2277235 eq2266493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266493 eq2277235
  have eq2277818 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2276366
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2276366
    | exact resolve eq2276366 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276366
  have eq2277820 : x = (k x x) := by
    first
    | exact superpose eq2276312 eq2277238
    | exact resolve eq2277238 eq2276312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276312 eq2277238
  have eq2282689 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq388 x
       have i₂ := eq2277820
       grind)
    | exact superpose eq2277820 eq388
    | (have j0 := eq388 x
       grind)
    | exact resolve eq388 eq2277820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq2277820
  have eq2282707 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2282689
  have eq2282724 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2282707
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2282707
    | exact resolve eq2282707 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2282707
  have eq2282816 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2267684 eq2282724
    | exact resolve eq2282724 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267684 eq2282724
  have eq2282903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2277818 eq2282816
    | exact resolve eq2282816 eq2277818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277818 eq2282816
  have eq2282987 : False := by grind
  exact eq2282987

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(Y,X) else if m(X,X) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_x_y_pxx_y_pyx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : (M.op x y) = (M.op x y) := by grind
  have eq21 : (M.op x y) = (M.op x y) := by grind
  clear eq20
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq23 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq22
  have eq24 : (σ x) = (σ x) := by grind
  have eq25 : (σ x) = (σ x) := by grind
  clear eq24
  have eq26 : (σ y) = (σ y) := by grind
  have eq27 : (σ y) = (σ y) := by grind
  clear eq26
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq29 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq28
  have eq30 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq31 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq46 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq52 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq64 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  have eq65 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq52
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq39
    | (have j0 := eq39 x
       grind)
    | exact resolve eq39 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq39
    | (have j0 := eq39 y
       grind)
    | exact resolve eq39 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq47
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq47
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq47 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq86
    | exact resolve eq86 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq94 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq108 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq99
  have eq257 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq387 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq388 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq389 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq387 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq387
    | (have j0 := eq387 X0
       grind)
    | exact resolve eq387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq2917 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq388 (τ X0)
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq388
    | (have j0 := eq388 (τ X0)
       grind)
    | exact resolve eq388 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2924 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2917 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2917
    | (have j0 := eq2917 X0
       grind)
    | exact resolve eq2917 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2917
  have eq2930 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2924 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2924
    | (have j0 := eq2924 X0
       grind)
    | exact resolve eq2924 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2924
  have eq3167 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq389 (τ X0)
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq389
    | (have j0 := eq389 (τ X0)
       grind)
    | exact resolve eq389 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq3177 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3167 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3167
    | (have j0 := eq3167 X0
       grind)
    | exact resolve eq3167 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167
  have eq3192 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3177 X0
       have i₂ := eq41 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq41 eq3177
    | (have j0 := eq3177 X0
       grind)
    | exact resolve eq3177 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq3177
  have eq3205 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3192 X0
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq3192
    | (have j0 := eq3192 X0
       grind)
    | exact resolve eq3192 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3192
  have eq3212 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3205 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3205
    | (have j0 := eq3205 X0
       grind)
    | exact resolve eq3205 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205
  have eq3219 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3212 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3212
    | (have j0 := eq3212 X0
       grind)
    | exact resolve eq3212 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3212
  have eq5724 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq257 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq257
    | exact resolve eq257 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq5822 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (k X0 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5724 X0
       have i₂ := eq10 X0 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5724
    | (have j0 := eq5724 X0
       grind)
    | exact resolve eq5724 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5724
  have eq15382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq15383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15382
    | exact resolve eq15382 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15382
  have eq15394 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq15383
       have r₂ := eq30
       grind)
    | exact resolve eq15383 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15383
  have eq15396 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15394 eq65
    | exact resolve eq65 eq15394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq15394
  have eq15400 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq15396
  have eq15402 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq15400
    | exact resolve eq15400 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15400
  have eq15603 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15402 eq108
    | exact resolve eq108 eq15402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq15402
  have eq15607 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq15603
  have eq15609 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq15607
    | exact resolve eq15607 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15607
  have eq15623 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  have eq15631 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15623
  have eq15660 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq15631
       grind)
    | exact superpose eq15631 eq64
    | exact resolve eq64 eq15631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15662 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15631
  have eq15665 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq15660
  have eq15666 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15662
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq15662
    | exact resolve eq15662 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15662
  have eq15667 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15665
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq15665
    | exact resolve eq15665 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15665
  have eq15867 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq15666
       grind)
    | exact superpose eq15666 eq72
    | exact resolve eq72 eq15666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15666
  have eq15887 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq15867
    | exact resolve eq15867 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15867
  have eq15906 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15667 eq3219
    | (have j0 := eq3219 (σ x)
       grind)
    | exact resolve eq3219 eq15667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3219
  have eq15908 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15906
    | exact resolve eq15906 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15906
  have eq70957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15908 eq15887
    | exact resolve eq15887 eq15908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15887 eq15908
  have eq70960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq70957
  have eq70969 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq70960
       have r₂ := eq30
       grind)
    | exact resolve eq70960 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70960
  have eq70975 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq71001 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq70975 eq15667
    | exact resolve eq15667 eq70975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15667 eq70975
  have eq71020 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq71001
  have eq71037 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq71020 eq70969
    | exact resolve eq70969 eq71020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70969 eq71020
  have eq71043 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq71037
  have eq71061 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq71069 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq71061
  have eq71839 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq71069
  have eq72615 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71043
       have i₂ := eq71839
       grind)
    | exact superpose eq71839 eq71043
    | exact resolve eq71043 eq71839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71043 eq71839
  have eq72622 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72615
  have eq72634 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq72622
       grind)
    | exact superpose eq72622 eq94
    | exact resolve eq94 eq72622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72635 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72622
  have eq72637 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq72635
  have eq72638 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq72634
  have eq72640 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72637
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq72637
    | exact resolve eq72637 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72637
  have eq72641 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72638
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq72638
    | exact resolve eq72638 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72638
  have eq73261 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq77014 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq72640
       grind)
    | exact superpose eq72640 eq72
    | exact resolve eq72 eq72640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72640
  have eq77057 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq77014
    | exact resolve eq77014 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77014
  have eq77062 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq73261
  have eq105322 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq77062 eq72641
    | exact resolve eq72641 eq77062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72641 eq77062
  have eq105373 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq105322
  have eq106104 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq105373
  have eq106106 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq106104
  have eq106109 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq106106
    | exact resolve eq106106 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106106
  have eq106510 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq106109 eq77057
    | exact resolve eq77057 eq106109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq106510
  have eq106524 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq106513
       have r₂ := eq30
       grind)
    | exact resolve eq106513 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106513
  have eq106530 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq106524
  have eq106535 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq106530
    | exact resolve eq106530 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106530
  have eq106557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq106535 eq77057
    | exact resolve eq77057 eq106535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77057 eq106535
  have eq106560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq106557
  have eq106571 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq106560
       have r₂ := eq30
       grind)
    | exact resolve eq106560 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106560
  have eq106577 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq106571
  have eq106583 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq106577
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq106577
    | exact resolve eq106577 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106577
  have eq107468 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq106583
       grind)
    | exact superpose eq106583 eq72
    | exact resolve eq72 eq106583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106583
  have eq107511 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq107468
    | exact resolve eq107468 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107468
  have eq108450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq107511 eq106109
    | exact resolve eq106109 eq107511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106109
  have eq108455 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq108450
  have eq108473 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq108455
       have r₂ := eq30
       grind)
    | exact resolve eq108455 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108455
  have eq108548 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq108473
  have eq108553 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq108548
    | exact resolve eq108548 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108548
  have eq109315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq108553 eq107511
    | exact resolve eq107511 eq108553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107511 eq108553
  have eq109318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq109315
  have eq109331 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq109318
       have r₂ := eq30
       grind)
    | exact resolve eq109318 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109318
  have eq109335 : (k x x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq110047 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46
       have i₂ := eq109335
       grind)
    | exact superpose eq109335 eq46
    | exact resolve eq46 eq109335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq110063 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15609
       have i₂ := eq109335
       grind)
    | exact superpose eq109335 eq15609
    | exact resolve eq15609 eq109335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15609 eq109335
  have eq110100 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq110063
  have eq110114 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq110047
       have i₂ := eq109331
       grind)
    | exact superpose eq109331 eq110047
    | exact resolve eq110047 eq109331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110047
  have eq110237 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq110114
  have eq110243 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq110237
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq110237
    | exact resolve eq110237 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110237
  have eq110280 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq110243 eq2930
    | (have j0 := eq2930 (σ x)
       grind)
    | (have r₁ := eq2930 (σ x)
       have r₂ := eq110243
       grind)
    | exact resolve eq2930 eq110243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2930 eq110243
  have eq110287 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq110280
  have eq2064207 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq109331
       have i₂ := eq110100
       grind)
    | exact superpose eq110100 eq109331
    | exact resolve eq109331 eq110100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110100
  have eq2065531 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2064207
  have eq2066199 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  have eq2066212 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2066199
  have eq2068277 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2066212
  have eq2070441 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2065531
       have i₂ := eq2068277
       grind)
    | exact superpose eq2068277 eq2065531
    | exact resolve eq2065531 eq2068277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065531 eq2068277
  have eq2070452 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2070441
  have eq2070507 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq2070452
       grind)
    | exact superpose eq2070452 eq94
    | exact resolve eq94 eq2070452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq2070516 : (σ (M.op x y)) = (σ (k y x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5822 y
       have i₂ := eq2070452
       grind)
    | exact superpose eq2070452 eq5822
    | exact resolve eq5822 eq2070452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5822 eq2070452
  have eq2070524 : (σ (M.op x y)) = (σ (k y x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq2070516
  have eq2070533 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2070507
  have eq2070539 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2070524
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq2070524
    | exact resolve eq2070524 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq2070524
  have eq2070546 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2070533
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2070533
    | exact resolve eq2070533 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070533
  have eq2070549 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2070539
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq2070539
    | exact resolve eq2070539 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070539
  have eq2070553 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23 eq2070549
    | exact resolve eq2070549 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070549
  have eq2072680 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq2092990 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2072680
  have eq2260984 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2092990 eq2070546
    | exact resolve eq2070546 eq2092990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070546 eq2092990
  have eq2261107 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2260984
  have eq2261164 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2261107
  have eq2261166 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq2261164
  have eq2261175 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq29 eq2261166
    | exact resolve eq2261166 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261166
  have eq2262311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2261175 eq2070553
    | exact resolve eq2070553 eq2261175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070553 eq2261175
  have eq2262316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2262311
  have eq2262333 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2262316
       have r₂ := eq30
       grind)
    | exact resolve eq2262316 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262316
  have eq2262345 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2262333 eq110287
    | exact resolve eq110287 eq2262333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110287 eq2262333
  have eq2263605 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2262345
  have eq2264097 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109331
       have i₂ := eq2263605
       grind)
    | exact superpose eq2263605 eq109331
    | exact resolve eq109331 eq2263605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109331 eq2263605
  have eq2265427 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2264097
  have eq2266014 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2265427 eq32
    | exact resolve eq32 eq2265427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2265427
  have eq2266485 : x = y ∨ x = y := by
    first
    | exact superpose eq31 eq2266014
    | exact resolve eq2266014 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2266014
  have eq2266486 : x = y := by grind
  clear eq2266485
  have eq2266493 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq21
       have i₂ := eq2266486
       grind)
    | exact superpose eq2266486 eq21
    | exact resolve eq21 eq2266486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2266494 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27
       have i₂ := eq2266486
       grind)
    | exact superpose eq2266486 eq27
    | exact resolve eq27 eq2266486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2266486
  have eq2267678 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2266494
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2266494
    | exact resolve eq2266494 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266494
  have eq2267684 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2267678 eq29
    | exact resolve eq29 eq2267678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2267678
  have eq2268224 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq2266493
       grind)
    | exact superpose eq2266493 eq64
    | exact resolve eq64 eq2266493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq2268910 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  have eq2268923 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23 eq2268224
    | exact resolve eq2268224 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268224
  have eq2269592 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  have eq2274435 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq2274454 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2267684 eq2274435
    | exact resolve eq2274435 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274435
  have eq2274502 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2274454
       have r₂ := eq30
       grind)
    | exact resolve eq2274454 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274454
  have eq2274527 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2267684 eq2274502
    | exact resolve eq2274502 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274502
  have eq2274553 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2274527 eq2269592
    | exact resolve eq2269592 eq2274527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269592 eq2274527
  have eq2274555 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2267684 eq2274553
    | exact resolve eq2274553 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274553
  have eq2276287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2274555 eq2268923
    | exact resolve eq2268923 eq2274555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268923 eq2274555
  have eq2276305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2276287
  have eq2276312 : x = (M.op x y) := by
    first
    | (have r₁ := eq2276305
       have r₂ := eq30
       grind)
    | exact resolve eq2276305 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276305
  have eq2276366 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2276312 eq23
    | exact resolve eq23 eq2276312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq2277235 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq2276312 eq2268910
    | exact resolve eq2268910 eq2276312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268910
  have eq2277238 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq2277235
       have i₂ := eq2266493
       grind)
    | exact superpose eq2266493 eq2277235
    | exact resolve eq2277235 eq2266493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266493 eq2277235
  have eq2277818 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2276366
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2276366
    | exact resolve eq2276366 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276366
  have eq2277820 : x = (k x x) := by
    first
    | exact superpose eq2276312 eq2277238
    | exact resolve eq2277238 eq2276312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276312 eq2277238
  have eq2282689 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq388 x
       have i₂ := eq2277820
       grind)
    | exact superpose eq2277820 eq388
    | (have j0 := eq388 x
       grind)
    | exact resolve eq388 eq2277820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq2277820
  have eq2282707 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2282689
  have eq2282724 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2282707
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2282707
    | exact resolve eq2282707 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2282707
  have eq2282816 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2267684 eq2282724
    | exact resolve eq2282724 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267684 eq2282724
  have eq2282903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2277818 eq2282816
    | exact resolve eq2282816 eq2277818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277818 eq2282816
  have eq2282987 : False := by grind
  exact eq2282987

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(Y,Y) else if m(X,X) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_x_y_pxx_y_pyx_pyy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : (M.op x y) = (M.op x y) := by grind
  have eq21 : (M.op x y) = (M.op x y) := by grind
  clear eq20
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq23 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq22
  have eq24 : (σ x) = (σ x) := by grind
  have eq25 : (σ x) = (σ x) := by grind
  clear eq24
  have eq26 : (σ y) = (σ y) := by grind
  have eq27 : (σ y) = (σ y) := by grind
  clear eq26
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq29 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq28
  have eq30 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq31 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq46 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq52 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq64 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  have eq65 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq52
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq39
    | (have j0 := eq39 x
       grind)
    | exact resolve eq39 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq39
    | (have j0 := eq39 y
       grind)
    | exact resolve eq39 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq47
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq47
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq47 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq86
    | exact resolve eq86 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq94 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq108 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq99
  have eq257 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq387 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq388 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq389 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq387 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq387
    | (have j0 := eq387 X0
       grind)
    | exact resolve eq387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq2917 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq388 (τ X0)
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq388
    | (have j0 := eq388 (τ X0)
       grind)
    | exact resolve eq388 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2924 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2917 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2917
    | (have j0 := eq2917 X0
       grind)
    | exact resolve eq2917 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2917
  have eq2930 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2924 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2924
    | (have j0 := eq2924 X0
       grind)
    | exact resolve eq2924 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2924
  have eq3167 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq389 (τ X0)
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq389
    | (have j0 := eq389 (τ X0)
       grind)
    | exact resolve eq389 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq3177 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3167 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3167
    | (have j0 := eq3167 X0
       grind)
    | exact resolve eq3167 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167
  have eq3192 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3177 X0
       have i₂ := eq41 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq41 eq3177
    | (have j0 := eq3177 X0
       grind)
    | exact resolve eq3177 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq3177
  have eq3205 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3192 X0
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq3192
    | (have j0 := eq3192 X0
       grind)
    | exact resolve eq3192 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3192
  have eq3212 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3205 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3205
    | (have j0 := eq3205 X0
       grind)
    | exact resolve eq3205 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205
  have eq3219 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3212 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3212
    | (have j0 := eq3212 X0
       grind)
    | exact resolve eq3212 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3212
  have eq5724 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq257 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq257
    | exact resolve eq257 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq5822 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (k X0 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5724 X0
       have i₂ := eq10 X0 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5724
    | (have j0 := eq5724 X0
       grind)
    | exact resolve eq5724 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5724
  have eq15382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq15383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15382
    | exact resolve eq15382 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15382
  have eq15394 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq15383
       have r₂ := eq30
       grind)
    | exact resolve eq15383 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15383
  have eq15396 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15394 eq65
    | exact resolve eq65 eq15394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq15394
  have eq15400 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq15396
  have eq15402 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq15400
    | exact resolve eq15400 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15400
  have eq15603 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15402 eq108
    | exact resolve eq108 eq15402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq15402
  have eq15607 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq15603
  have eq15609 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq15607
    | exact resolve eq15607 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15607
  have eq15623 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  have eq15631 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15623
  have eq15660 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq15631
       grind)
    | exact superpose eq15631 eq64
    | exact resolve eq64 eq15631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15662 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15631
  have eq15665 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq15660
  have eq15666 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15662
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq15662
    | exact resolve eq15662 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15662
  have eq15667 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15665
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq15665
    | exact resolve eq15665 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15665
  have eq15867 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq15666
       grind)
    | exact superpose eq15666 eq72
    | exact resolve eq72 eq15666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15666
  have eq15887 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq15867
    | exact resolve eq15867 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15867
  have eq15906 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15667 eq3219
    | (have j0 := eq3219 (σ x)
       grind)
    | exact resolve eq3219 eq15667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3219
  have eq15908 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15906
    | exact resolve eq15906 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15906
  have eq70957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15908 eq15887
    | exact resolve eq15887 eq15908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15887 eq15908
  have eq70960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq70957
  have eq70969 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq70960
       have r₂ := eq30
       grind)
    | exact resolve eq70960 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70960
  have eq70975 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq71001 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq70975 eq15667
    | exact resolve eq15667 eq70975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15667 eq70975
  have eq71020 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq71001
  have eq71037 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq71020 eq70969
    | exact resolve eq70969 eq71020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70969 eq71020
  have eq71043 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq71037
  have eq71061 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq71069 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq71061
  have eq71839 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq71069
  have eq72615 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71043
       have i₂ := eq71839
       grind)
    | exact superpose eq71839 eq71043
    | exact resolve eq71043 eq71839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71043 eq71839
  have eq72622 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72615
  have eq72634 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq72622
       grind)
    | exact superpose eq72622 eq94
    | exact resolve eq94 eq72622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72635 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72622
  have eq72637 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq72635
  have eq72638 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq72634
  have eq72640 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72637
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq72637
    | exact resolve eq72637 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72637
  have eq72641 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72638
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq72638
    | exact resolve eq72638 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72638
  have eq73261 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq77014 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq72640
       grind)
    | exact superpose eq72640 eq72
    | exact resolve eq72 eq72640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72640
  have eq77057 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq77014
    | exact resolve eq77014 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77014
  have eq77062 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq73261
  have eq105322 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq77062 eq72641
    | exact resolve eq72641 eq77062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72641 eq77062
  have eq105373 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq105322
  have eq106104 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq105373
  have eq106106 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq106104
  have eq106109 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq106106
    | exact resolve eq106106 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106106
  have eq106510 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq106109 eq77057
    | exact resolve eq77057 eq106109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq106510
  have eq106524 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq106513
       have r₂ := eq30
       grind)
    | exact resolve eq106513 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106513
  have eq106530 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq106524
  have eq106535 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq106530
    | exact resolve eq106530 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106530
  have eq106557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq106535 eq77057
    | exact resolve eq77057 eq106535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77057 eq106535
  have eq106560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq106557
  have eq106571 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq106560
       have r₂ := eq30
       grind)
    | exact resolve eq106560 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106560
  have eq106577 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq106571
  have eq106583 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq106577
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq106577
    | exact resolve eq106577 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106577
  have eq107468 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq106583
       grind)
    | exact superpose eq106583 eq72
    | exact resolve eq72 eq106583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106583
  have eq107511 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq107468
    | exact resolve eq107468 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107468
  have eq108450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq107511 eq106109
    | exact resolve eq106109 eq107511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106109
  have eq108455 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq108450
  have eq108473 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq108455
       have r₂ := eq30
       grind)
    | exact resolve eq108455 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108455
  have eq108548 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq108473
  have eq108553 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq108548
    | exact resolve eq108548 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108548
  have eq109315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq108553 eq107511
    | exact resolve eq107511 eq108553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107511 eq108553
  have eq109318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq109315
  have eq109331 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq109318
       have r₂ := eq30
       grind)
    | exact resolve eq109318 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109318
  have eq109335 : (k x x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq110047 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46
       have i₂ := eq109335
       grind)
    | exact superpose eq109335 eq46
    | exact resolve eq46 eq109335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq110063 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15609
       have i₂ := eq109335
       grind)
    | exact superpose eq109335 eq15609
    | exact resolve eq15609 eq109335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15609 eq109335
  have eq110100 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq110063
  have eq110114 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq110047
       have i₂ := eq109331
       grind)
    | exact superpose eq109331 eq110047
    | exact resolve eq110047 eq109331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110047
  have eq110237 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq110114
  have eq110243 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq110237
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq110237
    | exact resolve eq110237 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110237
  have eq110280 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq110243 eq2930
    | (have j0 := eq2930 (σ x)
       grind)
    | (have r₁ := eq2930 (σ x)
       have r₂ := eq110243
       grind)
    | exact resolve eq2930 eq110243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2930 eq110243
  have eq110287 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq110280
  have eq2064207 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq109331
       have i₂ := eq110100
       grind)
    | exact superpose eq110100 eq109331
    | exact resolve eq109331 eq110100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110100
  have eq2065531 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2064207
  have eq2066199 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  have eq2066212 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2066199
  have eq2068277 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2066212
  have eq2070441 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2065531
       have i₂ := eq2068277
       grind)
    | exact superpose eq2068277 eq2065531
    | exact resolve eq2065531 eq2068277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065531 eq2068277
  have eq2070452 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2070441
  have eq2070507 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq2070452
       grind)
    | exact superpose eq2070452 eq94
    | exact resolve eq94 eq2070452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq2070516 : (σ (M.op x y)) = (σ (k y x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5822 y
       have i₂ := eq2070452
       grind)
    | exact superpose eq2070452 eq5822
    | exact resolve eq5822 eq2070452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5822 eq2070452
  have eq2070524 : (σ (M.op x y)) = (σ (k y x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq2070516
  have eq2070533 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2070507
  have eq2070539 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2070524
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq2070524
    | exact resolve eq2070524 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq2070524
  have eq2070546 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2070533
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2070533
    | exact resolve eq2070533 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070533
  have eq2070549 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2070539
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq2070539
    | exact resolve eq2070539 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070539
  have eq2070553 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23 eq2070549
    | exact resolve eq2070549 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070549
  have eq2072680 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq2092990 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2072680
  have eq2260984 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2092990 eq2070546
    | exact resolve eq2070546 eq2092990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070546 eq2092990
  have eq2261107 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2260984
  have eq2261164 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2261107
  have eq2261166 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq2261164
  have eq2261175 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq29 eq2261166
    | exact resolve eq2261166 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261166
  have eq2262311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2261175 eq2070553
    | exact resolve eq2070553 eq2261175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070553 eq2261175
  have eq2262316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2262311
  have eq2262333 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2262316
       have r₂ := eq30
       grind)
    | exact resolve eq2262316 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262316
  have eq2262345 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2262333 eq110287
    | exact resolve eq110287 eq2262333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110287 eq2262333
  have eq2263605 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2262345
  have eq2264097 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109331
       have i₂ := eq2263605
       grind)
    | exact superpose eq2263605 eq109331
    | exact resolve eq109331 eq2263605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109331 eq2263605
  have eq2265427 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2264097
  have eq2266014 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2265427 eq32
    | exact resolve eq32 eq2265427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2265427
  have eq2266485 : x = y ∨ x = y := by
    first
    | exact superpose eq31 eq2266014
    | exact resolve eq2266014 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2266014
  have eq2266486 : x = y := by grind
  clear eq2266485
  have eq2266493 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq21
       have i₂ := eq2266486
       grind)
    | exact superpose eq2266486 eq21
    | exact resolve eq21 eq2266486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2266494 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27
       have i₂ := eq2266486
       grind)
    | exact superpose eq2266486 eq27
    | exact resolve eq27 eq2266486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2266486
  have eq2267678 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2266494
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2266494
    | exact resolve eq2266494 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266494
  have eq2267684 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2267678 eq29
    | exact resolve eq29 eq2267678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2267678
  have eq2268224 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq2266493
       grind)
    | exact superpose eq2266493 eq64
    | exact resolve eq64 eq2266493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq2268910 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  have eq2268923 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23 eq2268224
    | exact resolve eq2268224 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268224
  have eq2269592 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  have eq2274435 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq2274454 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2267684 eq2274435
    | exact resolve eq2274435 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274435
  have eq2274502 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2274454
       have r₂ := eq30
       grind)
    | exact resolve eq2274454 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274454
  have eq2274527 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2267684 eq2274502
    | exact resolve eq2274502 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274502
  have eq2274553 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2274527 eq2269592
    | exact resolve eq2269592 eq2274527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269592 eq2274527
  have eq2274555 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2267684 eq2274553
    | exact resolve eq2274553 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274553
  have eq2276287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2274555 eq2268923
    | exact resolve eq2268923 eq2274555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268923 eq2274555
  have eq2276305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2276287
  have eq2276312 : x = (M.op x y) := by
    first
    | (have r₁ := eq2276305
       have r₂ := eq30
       grind)
    | exact resolve eq2276305 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276305
  have eq2276366 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2276312 eq23
    | exact resolve eq23 eq2276312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq2277235 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq2276312 eq2268910
    | exact resolve eq2268910 eq2276312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268910
  have eq2277238 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq2277235
       have i₂ := eq2266493
       grind)
    | exact superpose eq2266493 eq2277235
    | exact resolve eq2277235 eq2266493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266493 eq2277235
  have eq2277818 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2276366
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2276366
    | exact resolve eq2276366 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276366
  have eq2277820 : x = (k x x) := by
    first
    | exact superpose eq2276312 eq2277238
    | exact resolve eq2277238 eq2276312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276312 eq2277238
  have eq2282689 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq388 x
       have i₂ := eq2277820
       grind)
    | exact superpose eq2277820 eq388
    | (have j0 := eq388 x
       grind)
    | exact resolve eq388 eq2277820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq2277820
  have eq2282707 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2282689
  have eq2282724 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2282707
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2282707
    | exact resolve eq2282707 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2282707
  have eq2282816 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2267684 eq2282724
    | exact resolve eq2282724 eq2267684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267684 eq2282724
  have eq2282903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2277818 eq2282816
    | exact resolve eq2282816 eq2277818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277818 eq2282816
  have eq2282987 : False := by grind
  exact eq2282987
