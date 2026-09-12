import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pxx_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq175 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ y)) = (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq538 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq175 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq558 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq538 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq538 X1 X0
       grind)
    | exact superpose eq538 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq538 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq538 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq538 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq538 X2 X0
       grind)
    | exact superpose eq538 eq16
    | exact resolve eq16 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq538 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq538 (M.op X1 X1) X0
       grind)
    | exact superpose eq538 eq16
    | exact resolve eq16 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq929 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq558 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq954 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (k X0 (M.op X1 X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq567 X2 X1 X0
       have i₂ := eq929 X0 X1
       grind)
    | exact superpose eq929 eq567
    | exact resolve eq567 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq982 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X1) (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq563 X2 X0 X1
       have i₂ := eq929 (M.op (M.op X0 X0) X1) X2
       grind)
    | exact superpose eq929 eq563
    | exact resolve eq563 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq1521 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq538 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq538 X0 X1
       grind)
    | exact superpose eq538 eq11
    | (have j0 := eq11 X0 (k X1 X1)
       grind)
    | exact resolve eq11 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1539 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq538
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1590 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1591 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1593 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1594 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1593 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1621 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1539 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1539
  have eq1628 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1521 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq1784 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1594 X1
       have i₂ := eq1621 X1 X0
       grind)
    | exact superpose eq1621 eq1594
    | (have j0 := eq1594 X1
       have j1 := eq1621 X1 X1
       grind)
    | (have r₁ := eq1594 (M.op X1 X1)
       have r₂ := eq1621 (M.op X1 X1) X1
       grind)
    | exact resolve eq1594 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621
  have eq1799 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1784 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1784
  have eq1947 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1628 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq2285 : ∀ X0 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) (M.op X2 (σ y))) = X2 := by
    intro X0 X2
    first
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq3350 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1590
       grind)
    | exact superpose eq1590 eq39
    | exact resolve eq39 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1590
  have eq3351 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq1799 x x
       grind)
    | (have r₁ := eq3350
       have r₂ := eq1799 y x
       grind)
    | (have r₁ := eq3350
       have r₂ := eq1799 x x
       grind)
    | exact resolve eq3350 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350
  have eq3353 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3351
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3351
    | exact resolve eq3351 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3351
  have eq3355 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq3353
    | exact resolve eq3353 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353
  have eq5130 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1591 eq3355
    | exact resolve eq3355 eq1591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1591 eq3355
  have eq5137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq1799 x x
       grind)
    | (have r₁ := eq5130
       have r₂ := eq1799 x x
       grind)
    | (have r₁ := eq5130
       have r₂ := eq1799 (σ y) (σ x)
       grind)
    | (have r₁ := eq5130
       have r₂ := eq1799 (σ x) (σ x)
       grind)
    | exact resolve eq5130 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799 eq5130
  have eq5141 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq5137
       have r₂ := eq27
       grind)
    | exact resolve eq5137 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5137
  have eq5380 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq5141 eq538
    | exact resolve eq538 eq5141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5141
  have eq5499 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq538 x X0
       have i₂ := eq5380 X1
       grind)
    | exact superpose eq5380 eq538
    | (have j1 := eq5380 X1
       grind)
    | exact resolve eq538 eq5380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq5380
  have eq5852 : ∀ X0 X1 : G, (σ x) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq929 (M.op X0 X0) X0
       have i₂ := eq5499 X1 (M.op X0 X0)
       grind)
    | (have i₁ := eq929 (M.op X1 X1) X1
       have i₂ := eq5499 (M.op X1 X1) X1
       grind)
    | exact superpose eq5499 eq929
    | (have j1 := eq5499 X1 X1
       grind)
    | exact resolve eq929 eq5499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5905 : ∀ X1 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op X1 X1) = x := by
    intro X1
    first
    | exact superpose eq5499 eq5852
    | (have j0 := eq5852 x X1
       have j1 := eq5499 X1 X1
       grind)
    | exact resolve eq5852 eq5499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5499 eq5852
  have eq6234 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) x) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq5905 eq141
    | (have j1 := eq5905 X0
       grind)
    | exact resolve eq141 eq5905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5905
  have eq6242 : ∀ X0 : G, x = (k x x) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq29 eq6234
    | (have j0 := eq6234 X0
       grind)
    | exact resolve eq6234 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6234
  have eq6245 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq6242 X0
       have j1 := eq1947 X0 x
       grind)
    | (have r₁ := eq6242 X0
       have r₂ := eq1947 X0 x
       grind)
    | exact resolve eq6242 eq1947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6242
  have eq6301 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq929 X0 X0
       have i₂ := eq6245 X0
       grind)
    | exact superpose eq6245 eq929
    | exact resolve eq929 eq6245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6332 : ∀ X0 : G, x = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq929 (M.op X0 X0) X0
       have i₂ := eq6245 (M.op X0 X0)
       grind)
    | exact superpose eq6245 eq929
    | exact resolve eq929 eq6245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6384 : x = (k x x) := by
    first
    | (have i₁ := eq6332 x
       have i₂ := eq6245 x
       grind)
    | exact superpose eq6245 eq6332
    | exact resolve eq6332 eq6245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6332
  have eq6509 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq6384
       grind)
    | exact superpose eq6384 eq39
    | exact resolve eq39 eq6384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq6517 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6509
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6509
    | exact resolve eq6509 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6509
  have eq6532 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq6517 eq1947
    | (have j0 := eq1947 X0 (σ x)
       grind)
    | (have r₁ := eq1947 X0 (σ x)
       have r₂ := eq6517
       grind)
    | exact resolve eq1947 eq6517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947
  have eq6533 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6517 eq1594
    | (have j0 := eq1594 (σ x)
       grind)
    | (have r₁ := eq1594 (σ x)
       have r₂ := eq6517
       grind)
    | exact resolve eq1594 eq6517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594 eq6517
  have eq6536 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6533
  have eq6537 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq6532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6532
  have eq6539 : x = (σ x) := by
    first
    | (have i₁ := eq6536
       have i₂ := eq6245 sF2
       grind)
    | exact superpose eq6245 eq6536
    | exact resolve eq6536 eq6245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6536
  have eq6543 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6539
       grind)
    | exact superpose eq6539 eq18
    | exact resolve eq18 eq6539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6829 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq929 X0 X0
       have i₂ := eq6537 X0
       grind)
    | exact superpose eq6537 eq929
    | exact resolve eq929 eq6537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq6831 : ∀ X1 X2 : G, (M.op (σ x) (k X1 (M.op X2 X2))) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq954 X1 X2 x
       have i₂ := eq6537 x
       grind)
    | exact superpose eq6537 eq954
    | exact resolve eq954 eq6537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq6839 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X1) (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq982 X0 X1 x
       have i₂ := eq6537 x
       grind)
    | exact superpose eq6537 eq982
    | exact resolve eq982 eq6537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq6929 : ∀ X1 : G, (k (M.op x X1) (σ x)) = X1 := by
    intro X1
    first
    | (have i₁ := eq6839 x X1
       have i₂ := eq6245 x
       grind)
    | exact superpose eq6245 eq6839
    | exact resolve eq6839 eq6245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6839
  have eq6936 : ∀ X1 : G, (M.op (σ x) (k X1 x)) = X1 := by
    intro X1
    first
    | (have i₁ := eq6831 X1 x
       have i₂ := eq6245 x
       grind)
    | exact superpose eq6245 eq6831
    | exact resolve eq6831 eq6245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6245 eq6831
  have eq7006 : ∀ X1 : G, (k (M.op (σ x) X1) (σ x)) = X1 := by
    intro X1
    first
    | (have i₁ := eq6929 X1
       have i₂ := eq6539
       grind)
    | exact superpose eq6539 eq6929
    | exact resolve eq6929 eq6539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6929
  have eq7013 : ∀ X1 : G, (M.op (σ x) (k X1 (σ x))) = X1 := by
    intro X1
    first
    | (have i₁ := eq6936 X1
       have i₂ := eq6539
       grind)
    | exact superpose eq6539 eq6936
    | exact resolve eq6936 eq6539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6936
  have eq7244 : ∀ X0 : G, (M.op (M.op (M.op (k x x) (M.op (σ x) (σ y))) (σ x)) (M.op X0 (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2285 x X0
       have i₂ := eq6301 x
       grind)
    | exact superpose eq6301 eq2285
    | exact resolve eq2285 eq6301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2285 eq6301
  have eq7292 : ∀ X0 : G, (M.op (k (M.op (k x x) (M.op (σ x) (σ y))) (σ x)) (M.op X0 (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq6829 eq7244
    | exact resolve eq7244 eq6829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7244
  have eq7368 : ∀ X0 : G, (M.op (k (M.op x (M.op (σ x) (σ y))) (σ x)) (M.op X0 (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7292 X0
       have i₂ := eq6384
       grind)
    | exact superpose eq6384 eq7292
    | exact resolve eq7292 eq6384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6384 eq7292
  have eq7431 : ∀ X0 : G, (M.op (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) (M.op X0 (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7368 X0
       have i₂ := eq6539
       grind)
    | exact superpose eq6539 eq7368
    | exact resolve eq7368 eq6539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7368
  have eq7489 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7431 X0
       have i₂ := eq7006 (k (M.op sF2 sF4) sF2)
       grind)
    | exact superpose eq7006 eq7431
    | exact resolve eq7431 eq7006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7006 eq7431
  have eq7714 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq7489 sF3
       have i₂ := eq6537 sF3
       grind)
    | exact superpose eq6537 eq7489
    | exact resolve eq7489 eq6537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6537 eq7489
  have eq7757 : (σ y) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq6829 eq7714
    | exact resolve eq7714 eq6829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6829 eq7714
  have eq7813 : (τ (σ y)) = (k (τ (M.op (σ x) (σ y))) x) := by
    first
    | exact superpose eq7757 eq141
    | exact resolve eq141 eq7757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq7757
  have eq7815 : (τ (σ y)) = (k (τ (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq7813
       have i₂ := eq6539
       grind)
    | exact superpose eq6539 eq7813
    | exact resolve eq7813 eq6539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6539 eq7813
  have eq7816 : y = (k (τ (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq31 eq7815
    | exact resolve eq7815 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq7815
  have eq8346 : (τ (M.op (σ x) (σ y))) = (M.op (σ x) y) := by
    first
    | exact superpose eq7816 eq7013
    | exact resolve eq7013 eq7816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7013 eq7816
  have eq8364 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6543 eq8346
    | exact resolve eq8346 eq6543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6543 eq8346
  have eq8380 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8364 eq14
    | exact resolve eq14 eq8364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8364
  have eq8381 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8380
    | exact resolve eq8380 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8380
  have eq8384 : False := by grind
  exact eq8384

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_x_pyy_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq60 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq321 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq336 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq60 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq60 eq60
    | exact resolve eq60 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq60 X2 X3 X0
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq336 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq336 X1 X0
       grind)
    | exact superpose eq336 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq336 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq336 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 X2
       have i₂ := eq336 X0 X2
       grind)
    | (have i₁ := eq14 X2 X1 X2
       have i₂ := eq336 X2 X0
       grind)
    | exact superpose eq336 eq14
    | exact resolve eq14 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 (M.op X1 X1) X1 X2
       have i₂ := eq336 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq60 (M.op X1 X1) X1 X2
       have i₂ := eq336 (M.op X1 X1) X0
       grind)
    | exact superpose eq336 eq60
    | exact resolve eq60 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq336 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq336 X0 X1
       grind)
    | exact superpose eq336 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq336 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq336 X1 X1
       grind)
    | exact resolve eq12 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq365 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq516 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq60 X2 X3 X0
       grind)
    | exact superpose eq60 eq63
    | exact resolve eq63 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) (M.op X4 X2)) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 X4 x X2
       have i₂ := eq63 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq63 X2 X2 X2 x
       grind)
    | exact superpose eq63 eq14
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 x
       have i₂ := eq63 X1 X0 y x
       grind)
    | (have i₁ := eq61 (M.op y y)
       have i₂ := eq63 y y y x
       grind)
    | exact superpose eq63 eq61
    | exact resolve eq61 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq556 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op X2 (M.op X4 X4)) X1)) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq60 X2 X4 (M.op (M.op X3 X3) (M.op (M.op X2 (M.op X4 X4)) X1))
       have i₂ := eq63 (M.op X2 (M.op X4 X4)) X3 X1 X0
       grind)
    | (have i₁ := eq60 X0 X1 (M.op X3 X3)
       have i₂ := eq63 X0 X1 (M.op X0 (M.op X1 X1)) X3
       grind)
    | exact superpose eq63 eq60
    | exact resolve eq60 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq63
  have eq649 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq348 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq658 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op X1 X1)
       have i₂ := eq649 (τ X0) X1
       grind)
    | exact superpose eq649 eq34
    | exact resolve eq34 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq659 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq321 X0 (M.op X1 X1)
       have i₂ := eq649 (σ X0) X1
       grind)
    | exact superpose eq649 eq321
    | exact resolve eq321 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq649
  have eq662 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq659 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq659
    | exact resolve eq659 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq663 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq658
    | exact resolve eq658 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq1033 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq74 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq74 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq74 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1060 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1063 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1033 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1064 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1063 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1067 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1064 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq1064
    | (have j0 := eq1064 X0 X1
       grind)
    | exact resolve eq1064 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq4941 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq663 (σ (M.op X1 X1)) X1
       have i₂ := eq371 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq371 eq663
    | (have j1 := eq371 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq663 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq4953 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq662 (τ (M.op X1 X1)) X1
       have i₂ := eq371 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq371 eq662
    | (have j1 := eq371 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq662 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4981 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq371 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq4985 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4953 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4953
  have eq4989 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4941 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4941
  have eq5117 : ∀ X0 X2 X3 : G, (M.op (M.op (τ (M.op X0 X0)) X2) (M.op X3 X3)) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq354 X3 x X2
       have i₂ := eq4985 x X0
       grind)
    | exact superpose eq4985 eq354
    | exact resolve eq354 eq4985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4985
  have eq5321 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op X2 X3)) X2) (M.op X0 X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq534 X1 X2 X3 X3
       have i₂ := eq336 X0 X3
       grind)
    | (have i₁ := eq534 X1 X2 X3 X3
       have i₂ := eq336 X3 X0
       grind)
    | exact superpose eq336 eq534
    | exact resolve eq534 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq534
  have eq5511 : ∀ X0 X2 X3 : G, (M.op (M.op (σ (M.op X0 X0)) X2) (M.op X3 X3)) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq354 X3 x X2
       have i₂ := eq4989 x X0
       grind)
    | exact superpose eq4989 eq354
    | exact resolve eq354 eq4989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq4989
  have eq8931 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op X2 (M.op (M.op X0 X2) (M.op X3 X3)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq516 X2 X1 (M.op X0 X2) X3 x
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq516
    | exact resolve eq516 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8968 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq339 X1 x X2 x
       have i₂ := eq516 X1 x X2 x X0
       grind)
    | exact superpose eq516 eq339
    | exact resolve eq339 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq13076 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 (M.op (M.op X1 X1) (M.op X2 (M.op X3 X3)))) (M.op X0 (M.op X5 X5))) = X2 := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq339 (M.op X0 (M.op X5 X5)) x X2 X3
       have i₂ := eq556 X1 (M.op X2 (M.op X3 X3)) X0 x X5
       grind)
    | (have i₁ := eq339 (M.op X0 X0) X1 X2 X3
       have i₂ := eq556 X0 (M.op X2 (M.op X3 X3)) (M.op X1 X1) X3 x
       grind)
    | exact superpose eq556 eq339
    | exact resolve eq339 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339 eq556
  have eq13693 : ∀ X0 X2 X5 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X5 X5))) = X2 := by
    intro X0 X2 X5
    first
    | (have i₁ := eq13076 X0 x X2 x X5
       have i₂ := eq355 x x X2
       grind)
    | exact superpose eq355 eq13076
    | exact resolve eq13076 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq13076
  have eq14569 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq13693 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13693
    | (have j0 := eq13693 x y X0
       grind)
    | exact resolve eq13693 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22443 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1067 X0 X1
       have j1 := eq1060 X0 X1
       grind)
    | (have r₁ := eq1067 X0 X1
       have r₂ := eq1060 X0 X1
       grind)
    | (have r₁ := eq1067 X1 X1
       have r₂ := eq1060 X1 X1
       grind)
    | exact resolve eq1067 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060 eq1067
  have eq22465 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22443 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq22443
    | exact resolve eq22443 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22546 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq22443 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22443
    | (have j0 := eq22443 x X0
       grind)
    | exact resolve eq22443 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22651 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22443 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22443
    | (have j0 := eq22443 X0 x
       grind)
    | exact resolve eq22443 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22443
  have eq22885 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22465 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq22465
    | (have j0 := eq22465 X0 X1
       grind)
    | exact resolve eq22465 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq22465
  have eq64080 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22546 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22546
    | (have j0 := eq22546 y
       grind)
    | exact resolve eq22546 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22546
  have eq64110 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq64080
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq64080
    | exact resolve eq64080 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64080
  have eq64127 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq64110
    | exact resolve eq64110 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64110
  have eq64892 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22885 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq22885
    | (have j0 := eq22885 X1 X1
       grind)
    | exact resolve eq22885 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22885
  have eq65488 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq64892 y x
       grind)
    | exact superpose eq64892 eq71
    | (have j1 := eq64892 x x
       grind)
    | exact resolve eq71 eq64892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq64892
  have eq65802 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65488
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq65488
    | exact resolve eq65488 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq65488
  have eq65831 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq65802
    | exact resolve eq65802 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65802
  have eq65848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq65831 eq64127
    | exact resolve eq64127 eq65831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64127 eq65831
  have eq65855 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq65848
       have r₂ := eq27
       grind)
    | exact resolve eq65848 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65848
  have eq65934 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq65855 eq662
    | exact resolve eq662 eq65855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq65855
  have eq66155 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28 eq65934
    | exact resolve eq65934 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq65934
  have eq66160 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq66155 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq66155 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq66155 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66155
  have eq66226 : ∀ X0 : G, x ≠ x ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4981 X0 x
       have i₂ := eq66160 x
       grind)
    | exact superpose eq66160 eq4981
    | (have j0 := eq4981 X0 x
       grind)
    | (have r₁ := eq4981 X0 x
       have r₂ := eq66160 x
       grind)
    | exact resolve eq4981 eq66160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4981 eq66160
  have eq66256 : ∀ X0 : G, x = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq66226 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66226
  have eq66656 : y = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq14569 x
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq14569
    | exact resolve eq14569 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14569
  have eq66779 : ∀ X0 : G, x = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5511 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq66256 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq66256 eq5511
    | exact resolve eq5511 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5511
  have eq66781 : ∀ X0 : G, x = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5117 X0 (τ (M.op X0 X0)) (τ (M.op X0 X0))
       have i₂ := eq66256 (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))
       grind)
    | exact superpose eq66256 eq5117
    | exact resolve eq5117 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5117
  have eq66782 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 X0)
       have i₂ := eq66256 (M.op X0 X0)
       grind)
    | exact superpose eq66256 eq14
    | exact resolve eq14 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66803 : ∀ X0 X1 : G, (M.op (M.op x X1) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8968 X0 (M.op X0 X0) X1
       have i₂ := eq66256 (M.op X0 X0)
       grind)
    | exact superpose eq66256 eq8968
    | exact resolve eq8968 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8968
  have eq66851 : ∀ X1 : G, (M.op (M.op x X1) x) = X1 := by
    intro X1
    first
    | (have i₁ := eq66803 x X1
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq66803
    | exact resolve eq66803 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66803
  have eq66871 : ∀ X1 : G, (M.op x (M.op X1 x)) = X1 := by
    intro X1
    first
    | (have i₁ := eq66782 x X1
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq66782
    | exact resolve eq66782 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66782
  have eq66872 : x = (τ x) := by
    first
    | (have i₁ := eq66781 x
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq66781
    | exact resolve eq66781 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66781
  have eq66874 : x = (σ x) := by
    first
    | (have i₁ := eq66779 x
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq66779
    | exact resolve eq66779 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66779
  have eq66962 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq66656
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq66656
    | exact resolve eq66656 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66656
  have eq67236 : x = (σ x) := by
    first
    | (have i₁ := eq66874
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq66874
    | exact resolve eq66874 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66874
  have eq67461 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq67236 eq26
    | exact resolve eq26 eq67236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq72591 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op X2 X3)) X2) x) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq5321 x X1 X2 X3
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq5321
    | exact resolve eq5321 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5321
  have eq72592 : ∀ X2 X3 : G, (M.op (M.op (M.op x (M.op X2 X3)) X2) x) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq72591 x X2 X3
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq72591
    | exact resolve eq72591 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72591
  have eq72690 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x x) (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1)) x) := by
    intro X0 X1
    first
    | exact superpose eq536 eq72592
    | exact resolve eq72592 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq72894 : ∀ X1 : G, (M.op x y) = (M.op (M.op (M.op x x) (M.op (M.op x (M.op X1 y)) X1)) x) := by
    intro X1
    first
    | (have i₁ := eq72690 x X1
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq72690
    | exact resolve eq72690 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72690
  have eq73071 : ∀ X1 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x (M.op X1 y)) X1)) x) := by
    intro X1
    first
    | (have i₁ := eq72894 X1
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq72894
    | exact resolve eq72894 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72894
  have eq73209 : ∀ X1 : G, (M.op x y) = (M.op (M.op x (M.op X1 y)) X1) := by
    intro X1
    first
    | (have i₁ := eq73071 X1
       have i₂ := eq66851 (M.op (M.op x (M.op X1 y)) X1)
       grind)
    | (have i₁ := eq73071 X1
       have i₂ := eq66851 (M.op (M.op x (M.op (M.op x (M.op X1 y)) X1)) x)
       grind)
    | exact superpose eq66851 eq73071
    | exact resolve eq73071 eq66851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73071
  have eq74226 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x (M.op X0 y)) (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13693 (M.op x (M.op X0 y)) X0 X1
       have i₂ := eq73209 X0
       grind)
    | exact superpose eq73209 eq13693
    | exact resolve eq13693 eq73209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73209
  have eq74307 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x (M.op X0 y)) x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq74226 X0 x
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq74226
    | exact resolve eq74226 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74226
  have eq74399 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq74307 X0
       have i₂ := eq66851 (M.op X0 y)
       grind)
    | (have i₁ := eq74307 X0
       have i₂ := eq66851 (M.op (M.op x (M.op X0 y)) x)
       grind)
    | exact superpose eq66851 eq74307
    | exact resolve eq74307 eq66851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74307
  have eq74585 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) y) = X0 := by
    intro X0
    first
    | exact superpose eq74399 eq13693
    | exact resolve eq13693 eq74399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74399
  have eq74768 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op (M.op x y) X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | exact superpose eq74585 eq13693
    | exact resolve eq13693 eq74585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13693 eq74585
  have eq74774 : ∀ X0 : G, y = (M.op X0 (M.op (M.op (M.op x y) X0) x)) := by
    intro X0
    first
    | (have i₁ := eq74768 X0 x
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq74768
    | exact resolve eq74768 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74768
  have eq79295 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op (M.op X0 X2) x))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8931 X0 X1 X2 x
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq8931
    | exact resolve eq8931 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8931
  have eq79296 : ∀ X0 X2 : G, (M.op x (M.op X2 (M.op (M.op X0 X2) x))) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq79295 X0 x X2
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq79295
    | exact resolve eq79295 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79295
  have eq79532 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) x) = (M.op X1 (M.op (M.op X0 X1) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq72592 x (M.op X1 (M.op (M.op X0 X1) x))
       have i₂ := eq79296 X0 X1
       grind)
    | exact superpose eq79296 eq72592
    | exact resolve eq72592 eq79296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72592
  have eq79533 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 (M.op (M.op X0 X1) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq79532 X0 X1
       have i₂ := eq66851 X0
       grind)
    | (have i₁ := eq79532 X0 X1
       have i₂ := eq66851 (M.op (M.op x X0) x)
       grind)
    | exact superpose eq66851 eq79532
    | exact resolve eq79532 eq66851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66851 eq79532
  have eq112585 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) x) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq67236 eq22651
    | (have j0 := eq22651 X0
       grind)
    | exact resolve eq22651 eq67236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22651
  have eq112586 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) x) ∨ (σ X0) = x := by
    intro X0
    first
    | (have i₁ := eq112585 X0
       have i₂ := eq66256 (σ X0)
       grind)
    | exact superpose eq66256 eq112585
    | (have j0 := eq112585 X0
       grind)
    | exact resolve eq112585 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112585
  have eq112616 : ∀ X0 : G, (σ (k x (τ X0))) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq112586 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq112586
    | exact resolve eq112586 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112707 : (σ (k x (M.op x y))) = (M.op (σ (M.op x y)) x) ∨ x = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq112586
    | (have j0 := eq112586 (M.op x y)
       grind)
    | exact resolve eq112586 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112586
  have eq112766 : (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) x) ∨ x = (σ (M.op x y)) := by
    first
    | exact superpose eq45 eq112707
    | exact resolve eq112707 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112707
  have eq112828 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq112616 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq112616
    | (have j0 := eq112616 X0
       grind)
    | exact resolve eq112616 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq112616
  have eq112870 : (k x (σ (M.op x y))) = (M.op (σ (M.op x y)) x) ∨ x = (σ (M.op x y)) := by
    first
    | exact superpose eq67236 eq112766
    | exact resolve eq112766 eq67236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112766
  have eq112932 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | exact superpose eq67236 eq112828
    | (have j0 := eq112828 X0
       grind)
    | exact resolve eq112828 eq67236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112828
  have eq113420 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq112932 sF0
       grind)
    | exact superpose eq112932 eq45
    | (have j1 := eq112932 (M.op x y)
       grind)
    | exact resolve eq45 eq112932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq112932
  have eq113439 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66962 eq113420
    | exact resolve eq113420 eq66962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66962 eq113420
  have eq113534 : (σ y) = (k x (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq67236 eq113439
    | exact resolve eq113439 eq67236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113439
  have eq113589 : (σ y) = (k x (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113534
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq113534
    | exact resolve eq113534 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113534
  have eq113674 : (σ y) = (M.op (σ (M.op x y)) x) ∨ x = (M.op x y) ∨ x = (σ (M.op x y)) := by
    first
    | exact superpose eq112870 eq113589
    | exact resolve eq113589 eq112870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112870 eq113589
  have eq118868 : (σ (M.op x y)) = (M.op x (M.op x (M.op (σ y) x))) ∨ x = (M.op x y) ∨ x = (σ (M.op x y)) := by
    first
    | exact superpose eq113674 eq79296
    | exact resolve eq79296 eq113674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79296 eq113674
  have eq118870 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (M.op x y) ∨ x = (σ (M.op x y)) := by
    first
    | (have i₁ := eq118868
       have i₂ := eq66871 sF3
       grind)
    | (have i₁ := eq118868
       have i₂ := eq66871 (M.op x (M.op sF3 x))
       grind)
    | exact superpose eq66871 eq118868
    | exact resolve eq118868 eq66871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66871 eq118868
  have eq118895 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ (M.op x y)) := by
    first
    | exact superpose eq67461 eq118870
    | exact resolve eq118870 eq67461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118870
  have eq118918 : x = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq118895
       have r₂ := eq27
       grind)
    | exact resolve eq118895 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118895
  have eq118957 : (M.op x y) = (τ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118918 eq30
    | exact resolve eq30 eq118918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq118918
  have eq119150 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118957
       have i₂ := eq66872
       grind)
    | exact superpose eq66872 eq118957
    | exact resolve eq118957 eq66872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66872 eq118957
  have eq119151 : x = (M.op x y) := by grind
  clear eq119150
  have eq119284 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq119151 eq20
    | exact resolve eq20 eq119151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq119393 : ∀ X0 : G, y = (M.op X0 (M.op (M.op x X0) x)) := by
    intro X0
    first
    | exact superpose eq119151 eq74774
    | exact resolve eq74774 eq119151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74774 eq119151
  have eq119437 : y = (M.op x x) := by
    first
    | (have i₁ := eq119393 x
       have i₂ := eq79533 x x
       grind)
    | exact superpose eq79533 eq119393
    | exact resolve eq119393 eq79533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79533 eq119393
  have eq119528 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq119284
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq119284
    | exact resolve eq119284 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119284
  have eq119537 : x = y := by
    first
    | (have i₁ := eq119437
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq119437
    | exact resolve eq119437 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119437
  have eq119616 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq67236 eq119528
    | exact resolve eq119528 eq67236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119528
  have eq120200 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq119537
       grind)
    | exact superpose eq119537 eq24
    | exact resolve eq24 eq119537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq119537
  have eq120430 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq120200
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq120200
    | exact resolve eq120200 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq120200
  have eq120519 : x = (σ y) := by
    first
    | exact superpose eq67236 eq120430
    | exact resolve eq120430 eq67236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67236 eq120430
  have eq122247 : (M.op (σ x) (σ y)) = (M.op x x) := by
    first
    | exact superpose eq120519 eq67461
    | exact resolve eq67461 eq120519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67461 eq120519
  have eq122301 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq122247
       have i₂ := eq66256 x
       grind)
    | exact superpose eq66256 eq122247
    | exact resolve eq122247 eq66256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66256 eq122247
  have eq122678 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq122301 eq27
    | exact resolve eq27 eq122301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq122301
  have eq122747 : False := by grind
  exact eq122747

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_pxy_pyx_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
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
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq55 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq660 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) (M.op X4 X2)) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 X4 x X2
       have i₂ := eq57 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq57 X2 X2 X2 x
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x
       have i₂ := eq57 X1 X0 y x
       grind)
    | (have i₁ := eq55 (M.op y y)
       have i₂ := eq57 y y y x
       grind)
    | exact superpose eq57 eq55
    | exact resolve eq55 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq663 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x
       have i₂ := eq57 X0 X1 sF3 x
       grind)
    | (have i₁ := eq56 (M.op sF3 sF3)
       have i₂ := eq57 sF3 sF3 sF3 x
       grind)
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq32486 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq32487 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq32486
    | exact resolve eq32486 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32486
  have eq32497 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq32487
       have r₂ := eq28
       grind)
    | exact resolve eq32487 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32487
  have eq32500 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq32497
    | exact resolve eq32497 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32497
  have eq32658 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq32500 eq660
    | exact resolve eq660 eq32500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32500
  have eq32664 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq663 eq32658
    | exact resolve eq32658 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq32658
  have eq32665 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq32664
  have eq32829 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq660 X0 X1 y y
       have i₂ := eq32665
       grind)
    | exact superpose eq32665 eq660
    | exact resolve eq660 eq32665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq32665
  have eq32835 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq662 eq32829
    | exact resolve eq32829 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq32829
  have eq32836 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq32835
  have eq32904 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq32836 eq30
    | exact resolve eq30 eq32836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32836
  have eq33016 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq32904
    | exact resolve eq32904 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32904
  have eq33017 : x = y := by grind
  clear eq33016
  have eq33190 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq33017
       grind)
    | exact superpose eq33017 eq19
    | exact resolve eq19 eq33017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq33191 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq33017
       grind)
    | exact superpose eq33017 eq25
    | exact resolve eq25 eq33017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq33017
  have eq33297 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq33191
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33191
    | exact resolve eq33191 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq33191
  have eq33312 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq33297 eq27
    | exact resolve eq27 eq33297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq33297
  have eq33727 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq33312 eq69
    | exact resolve eq69 eq33312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq33312
  have eq33922 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq33727
       have i₂ := eq33190
       grind)
    | exact superpose eq33190 eq33727
    | exact resolve eq33727 eq33190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33190 eq33727
  have eq33936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33922 eq15
    | exact resolve eq15 eq33922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33922
  have eq33981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq33936
    | exact resolve eq33936 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq33936
  have eq33990 : False := by grind
  exact eq33990

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq25 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq125 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq119 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq119 X0 X1
       grind)
    | exact resolve eq13 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq125 (σ X0) (σ X1)
       grind)
    | exact superpose eq125 eq15
    | (have j1 := eq125 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 X1
       have i₂ := eq125 X0 X1
       grind)
    | exact superpose eq125 eq134
    | (have j0 := eq134 X0 X1
       have j1 := eq125 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq134 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq134
  have eq347 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq119 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq119 (σ X1) X0
       grind)
    | exact superpose eq119 eq22
    | exact resolve eq22 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq119
  have eq2196 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq170 x y
       grind)
    | exact superpose eq170 eq16
    | (have j1 := eq170 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq170 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq170 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq170 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq2211 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2196
  have eq6526 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2211
       grind)
    | exact superpose eq2211 eq10
    | exact resolve eq10 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211
  have eq6539 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6526
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6526
    | exact resolve eq6526 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6526
  have eq6540 : x = y := by grind
  clear eq6539
  have eq16097 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6540
       grind)
    | exact superpose eq6540 eq16
    | exact resolve eq16 eq6540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6540
  have eq16098 : False := by grind
  exact eq16098

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_y_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq25 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq100 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq100 (σ X0) (σ X1)
       grind)
    | exact superpose eq100 eq15
    | (have j1 := eq100 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq109
    | (have j0 := eq109 X0 X1
       have j1 := eq100 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq109 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq109
  have eq317 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq95 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq95 (σ X1) X0
       grind)
    | exact superpose eq95 eq22
    | exact resolve eq22 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq95
  have eq2044 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq145 x y
       grind)
    | exact superpose eq145 eq16
    | (have j1 := eq145 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq145 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq145 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq145 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq2057 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2044
  have eq7787 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2057
       grind)
    | exact superpose eq2057 eq10
    | exact resolve eq10 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq7800 : x = y ∨ x = y := by
    first
    | (have i₁ := eq7787
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7787
    | exact resolve eq7787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7787
  have eq7801 : x = y := by grind
  clear eq7800
  have eq17737 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7801
       grind)
    | exact superpose eq7801 eq16
    | exact resolve eq16 eq7801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7801
  have eq17738 : False := by grind
  exact eq17738

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq55 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq661 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) (M.op X4 X2)) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 X4 x X2
       have i₂ := eq57 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq57 X2 X2 X2 x
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x
       have i₂ := eq57 X1 X0 y x
       grind)
    | (have i₁ := eq55 (M.op y y)
       have i₂ := eq57 y y y x
       grind)
    | exact superpose eq57 eq55
    | exact resolve eq55 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq664 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x
       have i₂ := eq57 X0 X1 sF3 x
       grind)
    | (have i₁ := eq56 (M.op sF3 sF3)
       have i₂ := eq57 sF3 sF3 sF3 x
       grind)
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq31958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq78 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq31959 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq31958
    | exact resolve eq31958 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31958
  have eq31969 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq31959
       have r₂ := eq28
       grind)
    | exact resolve eq31959 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31959
  have eq31972 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq31969
    | exact resolve eq31969 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31969
  have eq32129 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq31972 eq661
    | exact resolve eq661 eq31972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31972
  have eq32135 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq664 eq32129
    | exact resolve eq32129 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq32129
  have eq32136 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq32135
  have eq32300 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq661 X0 X1 y y
       have i₂ := eq32136
       grind)
    | exact superpose eq32136 eq661
    | exact resolve eq661 eq32136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq32136
  have eq32306 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq663 eq32300
    | exact resolve eq32300 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq32300
  have eq32307 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq32306
  have eq32375 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq32307 eq30
    | exact resolve eq30 eq32307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32307
  have eq32477 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq32375
    | exact resolve eq32375 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32375
  have eq32478 : x = y := by grind
  clear eq32477
  have eq32640 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq32478
       grind)
    | exact superpose eq32478 eq19
    | exact resolve eq19 eq32478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq32641 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq32478
       grind)
    | exact superpose eq32478 eq25
    | exact resolve eq25 eq32478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq32478
  have eq32747 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq32641
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32641
    | exact resolve eq32641 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq32641
  have eq32762 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32747 eq27
    | exact resolve eq27 eq32747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32747
  have eq33165 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32762 eq69
    | exact resolve eq69 eq32762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq32762
  have eq33358 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq33165
       have i₂ := eq32640
       grind)
    | exact superpose eq32640 eq33165
    | exact resolve eq33165 eq32640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32640 eq33165
  have eq33371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33358 eq15
    | exact resolve eq15 eq33358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33358
  have eq33416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq33371
    | exact resolve eq33371 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq33371
  have eq33425 : False := by grind
  exact eq33425

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_x_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq55 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq79
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79
    | exact resolve eq79 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq661 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) (M.op X4 X2)) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 X4 x X2
       have i₂ := eq57 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq57 X2 X2 X2 x
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x
       have i₂ := eq57 X1 X0 y x
       grind)
    | (have i₁ := eq55 (M.op y y)
       have i₂ := eq57 y y y x
       grind)
    | exact superpose eq57 eq55
    | exact resolve eq55 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq664 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x
       have i₂ := eq57 X0 X1 sF3 x
       grind)
    | (have i₁ := eq56 (M.op sF3 sF3)
       have i₂ := eq57 sF3 sF3 sF3 x
       grind)
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq32938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq32939 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq32938
    | exact resolve eq32938 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32938
  have eq32950 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq32939
       have r₂ := eq28
       grind)
    | exact resolve eq32939 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32939
  have eq32954 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq32950
    | exact resolve eq32950 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32950
  have eq33114 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq32954 eq661
    | exact resolve eq661 eq32954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32954
  have eq33120 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq664 eq33114
    | exact resolve eq33114 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq33114
  have eq33121 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq33120
  have eq33287 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq661 X0 X1 y y
       have i₂ := eq33121
       grind)
    | exact superpose eq33121 eq661
    | exact resolve eq661 eq33121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq33121
  have eq33293 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq663 eq33287
    | exact resolve eq33287 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq33287
  have eq33294 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq33293
  have eq33362 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq33294 eq30
    | exact resolve eq30 eq33294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq33294
  have eq33474 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq33362
    | exact resolve eq33362 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq33362
  have eq33475 : x = y := by grind
  clear eq33474
  have eq33640 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq33475
       grind)
    | exact superpose eq33475 eq19
    | exact resolve eq19 eq33475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq33641 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq33475
       grind)
    | exact superpose eq33475 eq25
    | exact resolve eq25 eq33475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq33475
  have eq33747 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq33641
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33641
    | exact resolve eq33641 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq33641
  have eq33762 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq33747 eq27
    | exact resolve eq27 eq33747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq33747
  have eq34181 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq33762 eq69
    | exact resolve eq69 eq33762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq33762
  have eq34378 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq34181
       have i₂ := eq33640
       grind)
    | exact superpose eq33640 eq34181
    | exact resolve eq34181 eq33640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33640 eq34181
  have eq34392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34378 eq15
    | exact resolve eq15 eq34378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34378
  have eq34437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq34392
    | exact resolve eq34392 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq34392
  have eq34446 : False := by grind
  exact eq34446

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq37 (τ X0)
       grind)
    | exact superpose eq37 eq17
    | exact resolve eq17 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq39
    | exact resolve eq39 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq41
    | exact resolve eq41 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq41
  have eq79 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (σ X0) (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq19
    | exact resolve eq19 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq230 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) ∨ (σ X0) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ (M.op X0 X0)) (M.op X1 (σ X0))
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq12
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ (M.op X0 X0)) (M.op X1 (σ X0))
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (M.op X1 (σ X0))
       grind)
    | exact resolve eq13 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) ≠ (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq231 X0 X1
       have i₂ := eq42 (M.op X0 X0)
       grind)
    | exact superpose eq42 eq231
    | (have j0 := eq231 X0 X1
       grind)
    | exact resolve eq231 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq231
  have eq250 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) ≠ (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq240 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq240 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq240
    | (have j0 := eq240 X0 X1
       grind)
    | exact resolve eq240 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq253 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) ≠ (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq250 X0 X1
       have j1 := eq230 X0 X1
       grind)
    | (have r₁ := eq250 X0 X1
       have r₂ := eq230 X0 X1
       grind)
    | exact resolve eq250 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq250
  have eq258 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq90
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ X1)) (M.op (σ X0) (σ X1))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq19 X0 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq19
    | (have j1 := eq90 X0 X1
       grind)
    | exact resolve eq19 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq299 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq258 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq258
    | (have j0 := eq258 X0 X1
       grind)
    | exact resolve eq258 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq310 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq299 X0 X1
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq299 X1 X0
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq299 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq1263 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq310
    | exact resolve eq310 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq1341 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1263 (M.op X1 (σ X0)) (σ (M.op X0 X0))
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq1263
    | exact resolve eq1263 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq1263
  have eq1474 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1341 X0 X1
       have j1 := eq253 X0 X1
       grind)
    | (have r₁ := eq1341 X0 X1
       have r₂ := eq253 X0 X1
       grind)
    | exact resolve eq1341 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq1341
  have eq1537 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (τ X0))) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1474 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1474
    | exact resolve eq1474 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq1566 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1537 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq1537
    | exact resolve eq1537 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1537
  have eq1584 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1566 (M.op X0 X1) (M.op x X0)
       have i₂ := eq19 x X0 X1
       grind)
    | exact superpose eq19 eq1566
    | exact resolve eq1566 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1566
  have eq2612 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1584 (σ X1) (σ X0)
       have i₂ := eq268 X1 X0 (σ X1)
       grind)
    | exact superpose eq268 eq1584
    | (have j1 := eq268 X1 X0 x
       grind)
    | exact resolve eq1584 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq1584
  have eq2701 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2612 X0 X1
       have j1 := eq81 X1 (σ X0)
       grind)
    | (have r₁ := eq2612 X0 X0
       have r₂ := eq81 X0 (σ X0)
       grind)
    | exact resolve eq2612 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq2612
  have eq2711 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2701 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2701
    | (have j0 := eq2701 X0 X1
       grind)
    | exact resolve eq2701 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2701
  have eq2712 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2711 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711
  have eq2715 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2712 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2712
    | exact resolve eq2712 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2733 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2712 y x
       grind)
    | exact superpose eq2712 eq16
    | exact resolve eq16 eq2712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2712
  have eq3295 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq2715 X0 (τ X1)
       grind)
    | exact superpose eq2715 eq17
    | exact resolve eq17 eq2715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2715
  have eq3359 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3295 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3295
    | exact resolve eq3295 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3295
  have eq3387 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3359 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3359
    | exact resolve eq3359 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3359
  have eq3478 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2733
       have i₂ := eq3387 x y
       grind)
    | exact superpose eq3387 eq2733
    | exact resolve eq2733 eq3387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2733 eq3387
  have eq3479 : False := by grind
  exact eq3479
