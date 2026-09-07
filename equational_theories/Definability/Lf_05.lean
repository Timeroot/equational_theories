import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pxy_y_pxy_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq43 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X1 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq12 X1 X2
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2
       have i₂ := eq12 X0 X2
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X1 X2) = X2 ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X1 X1 X2
       have j1 := eq50 X1 X1 X2
       grind)
    | (have r₁ := eq43 X0 X1 X2
       have r₂ := eq50 X0 X1 X2
       grind)
    | (have r₁ := eq43 X1 X0 X2
       have r₂ := eq50 X0 X1 X2
       grind)
    | (have r₁ := eq43 X0 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq50 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq43 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq50
  have eq97 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq115 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq249 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq116 (σ X0) (σ X1)
       grind)
    | exact superpose eq116 eq13
    | (have j1 := eq116 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq116 (τ X0) X1
       grind)
    | exact superpose eq116 eq15
    | (have j1 := eq116 (τ X0) X1
       grind)
    | exact resolve eq15 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq116
  have eq1623 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq251 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq251
    | exact resolve eq251 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq1695 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1623 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1623
    | (have j0 := eq1623 X0 X1
       grind)
    | exact resolve eq1623 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq2094 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq97
    | (have j0 := eq97 X1 (σ X0)
       grind)
    | (have r₁ := eq97 X0 (σ X0)
       have r₂ := eq26 X0
       grind)
    | exact resolve eq97 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq2124 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2094 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2094
    | (have j0 := eq2094 X0 X1
       grind)
    | exact resolve eq2094 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094
  have eq2973 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq249 x y
       grind)
    | exact superpose eq249 eq14
    | (have j1 := eq249 x y
       grind)
    | exact resolve eq14 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3003 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq4471 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2973
       have i₂ := eq1695 x y
       grind)
    | exact superpose eq1695 eq2973
    | (have j1 := eq1695 (σ x) (σ y)
       grind)
    | (have r₁ := eq2973
       have r₂ := eq1695 x y
       grind)
    | exact resolve eq2973 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2973
  have eq4472 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4471
  have eq4672 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4472
       grind)
    | exact superpose eq4472 eq14
    | exact resolve eq14 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4673 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq4472
       grind)
    | exact superpose eq4472 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq4472
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq4472
       grind)
    | exact resolve eq11 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4472
  have eq4674 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4673
  have eq4675 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4674
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq4674
    | exact resolve eq4674 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4674
  have eq4680 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4675
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq4675
    | exact resolve eq4675 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4675
  have eq4681 : (σ y) = (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4680
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq4680
    | exact resolve eq4680 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4680
  have eq50153 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1695 x y
       have i₂ := eq4681
       grind)
    | exact superpose eq4681 eq1695
    | (have j0 := eq1695 x y
       grind)
    | exact resolve eq1695 eq4681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4681
  have eq50196 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq50153
  have eq50220 : (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq50196
       have r₂ := eq4672
       grind)
    | exact resolve eq50196 eq4672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4672 eq50196
  have eq51111 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2124 X0 y
       have i₂ := eq50220
       grind)
    | exact superpose eq50220 eq2124
    | (have j0 := eq2124 X0 x
       grind)
    | (have r₁ := eq2124 x y
       have r₂ := eq50220
       grind)
    | (have r₁ := eq2124 y x
       have r₂ := eq50220
       grind)
    | exact resolve eq2124 eq50220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124 eq50220
  have eq128586 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq51111 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51111
  have eq128612 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq128586
       grind)
    | exact superpose eq128586 eq14
    | exact resolve eq14 eq128586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128586
  have eq128684 : y = (M.op x y) := by
    first
    | (have j1 := eq1695 x y
       grind)
    | (have r₁ := eq128612
       have r₂ := eq1695 x y
       grind)
    | exact resolve eq128612 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695 eq128612
  have eq128695 : y ≠ y ∨ (M.op x x) = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq128684
       grind)
    | exact superpose eq128684 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq128684
       grind)
    | exact resolve eq11 eq128684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128696 : y = (k x y) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq128695
  have eq128925 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq3003 x y
       have i₂ := eq128696
       grind)
    | exact superpose eq128696 eq3003
    | (have j0 := eq3003 x y
       grind)
    | exact resolve eq3003 eq128696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128696
  have eq129026 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq128925
  have eq129070 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq129026
       grind)
    | exact superpose eq129026 eq14
    | exact resolve eq14 eq129026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129026
  have eq129071 : (σ y) ≠ (σ y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq129070
       have i₂ := eq128684
       grind)
    | exact superpose eq128684 eq129070
    | exact resolve eq129070 eq128684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129070
  have eq129072 : (M.op x x) = (M.op y y) := by grind
  clear eq129071
  have eq129097 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq129072
       grind)
    | exact superpose eq129072 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq129072
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq129072
       grind)
    | exact resolve eq10 eq129072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129072
  have eq129328 : (M.op x y) = (k x y) := by
    first
    | (have j0 := eq129097 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129097
  have eq129331 : y = (k x y) := by
    first
    | (have i₁ := eq129328
       have i₂ := eq128684
       grind)
    | exact superpose eq128684 eq129328
    | exact resolve eq129328 eq128684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129328
  have eq129392 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3003 x y
       have i₂ := eq129331
       grind)
    | exact superpose eq129331 eq3003
    | (have j0 := eq3003 x y
       grind)
    | exact resolve eq3003 eq129331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003 eq129331
  have eq129493 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq129392
  have eq129544 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq129493
       grind)
    | exact superpose eq129493 eq14
    | exact resolve eq14 eq129493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129493
  have eq129548 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq129544
       have i₂ := eq128684
       grind)
    | exact superpose eq128684 eq129544
    | exact resolve eq129544 eq128684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128684 eq129544
  have eq129549 : False := by grind
  exact eq129549

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pxy_y_pyx_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (τ X0)
       have i₂ := eq21 (τ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq25
    | exact resolve eq25 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq56 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq84 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq54 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq8
    | (have j1 := eq54 X0 X1
       grind)
    | exact resolve eq8 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq207 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq195
    | (have j0 := eq195 X0 X1
       grind)
    | exact resolve eq195 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq1199 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq201 (τ X0) (τ X1)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq201
    | (have j0 := eq201 (τ X0) (τ X1)
       grind)
    | exact resolve eq201 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq201
  have eq1208 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1199 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq1199
    | (have j0 := eq1199 X0 X1
       grind)
    | exact resolve eq1199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1214 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1208 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1208
    | (have j0 := eq1208 X0 X1
       grind)
    | exact resolve eq1208 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1217 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1214 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq1214
    | (have j0 := eq1214 X0 X1
       grind)
    | exact resolve eq1214 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1218 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1217 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq1217
    | (have j0 := eq1217 X0 X1
       grind)
    | exact resolve eq1217 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1217
  have eq1219 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1218 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1218
    | (have j0 := eq1218 X0 X1
       grind)
    | exact resolve eq1218 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1220 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1219 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1219
    | (have j0 := eq1219 X0 X1
       grind)
    | exact resolve eq1219 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1321 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq46
    | exact resolve eq46 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1456 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1321 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1321
    | (have j0 := eq1321 X0 X1
       grind)
    | exact resolve eq1321 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1499 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq84
    | (have j0 := eq84 X1 (σ X0)
       grind)
    | (have r₁ := eq84 X0 (σ X0)
       have r₂ := eq26 X0
       grind)
    | exact resolve eq84 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1521 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1499 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1499
    | (have j0 := eq1499 X0 X1
       grind)
    | exact resolve eq1499 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1566 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq207 x y
       grind)
    | exact superpose eq207 eq14
    | (have j1 := eq207 x y
       grind)
    | exact resolve eq14 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1622 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq42208 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1566
       have i₂ := eq1456 x y
       grind)
    | exact superpose eq1456 eq1566
    | (have j1 := eq1456 x y
       grind)
    | (have r₁ := eq1566
       have r₂ := eq1456 x y
       grind)
    | exact resolve eq1566 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456 eq1566
  have eq42209 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq42208
  have eq42210 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq42209
  have eq42331 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq42210
       grind)
    | exact superpose eq42210 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq42210
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq42210
       grind)
    | exact resolve eq11 eq42210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42210
  have eq42332 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq42331
  have eq42334 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42332
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq42332
    | exact resolve eq42332 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42332
  have eq42335 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42334
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq42334
    | exact resolve eq42334 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq42334
  have eq42336 : (σ y) = (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42335
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq42335
    | exact resolve eq42335 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42335
  have eq89052 : (k x y) = (τ (σ y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq42336
       grind)
    | exact superpose eq42336 eq8
    | exact resolve eq8 eq42336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42336
  have eq89061 : (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (k x y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq89052
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq89052
    | exact resolve eq89052 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89052
  have eq89062 : (M.op y y) = (τ (σ (M.op x x))) ∨ y = (k x y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (M.op y y)
       have i₂ := eq89061
       grind)
    | exact superpose eq89061 eq8
    | exact resolve eq8 eq89061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89061
  have eq89071 : (M.op x x) = (M.op y y) ∨ y = (k x y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq89062
       have i₂ := eq8 (M.op x x)
       grind)
    | exact superpose eq8 eq89062
    | exact resolve eq89062 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89062
  have eq89072 : y = (k x y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq89071
  have eq89078 : y ≠ y ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1220 x y
       have i₂ := eq89072
       grind)
    | exact superpose eq89072 eq1220
    | (have j0 := eq1220 x y
       grind)
    | (have r₁ := eq1220 x y
       have r₂ := eq89072
       grind)
    | exact resolve eq1220 eq89072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq89072
  have eq89198 : y ≠ y ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq89078
  have eq89199 : (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq89198
  have eq89275 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq89199
       grind)
    | exact superpose eq89199 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq89199
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq89199
       grind)
    | exact resolve eq10 eq89199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89315 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1521 y X0
       have i₂ := eq89199
       grind)
    | exact superpose eq89199 eq1521
    | (have j0 := eq1521 X0 x
       grind)
    | exact resolve eq1521 eq89199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89199
  have eq89895 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq89275 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89275
  have eq90787 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq89315 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89315
  have eq90806 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq90787
       grind)
    | exact superpose eq90787 eq14
    | exact resolve eq14 eq90787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90787
  have eq90833 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq90806
       have i₂ := eq89895
       grind)
    | exact superpose eq89895 eq90806
    | exact resolve eq90806 eq89895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89895 eq90806
  have eq90852 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq90833
  have eq90853 : y = (M.op x y) := by grind
  clear eq90852
  have eq90855 : y ≠ y ∨ (M.op x x) = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq90853
       grind)
    | exact superpose eq90853 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq90853
       grind)
    | exact resolve eq11 eq90853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90862 : y = (k x y) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq90855
  have eq91018 : (σ y) ≠ (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1622 x y
       have i₂ := eq90862
       grind)
    | exact superpose eq90862 eq1622
    | (have j0 := eq1622 x y
       grind)
    | exact resolve eq1622 eq90862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622 eq90862
  have eq91340 : (σ y) ≠ (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq91018
  have eq91341 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq91340
  have eq91410 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq91341
       grind)
    | exact superpose eq91341 eq14
    | exact resolve eq14 eq91341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91341
  have eq91416 : (σ y) ≠ (σ y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq91410
       have i₂ := eq90853
       grind)
    | exact superpose eq90853 eq91410
    | exact resolve eq91410 eq90853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91410
  have eq91417 : (M.op x x) = (M.op y y) := by grind
  clear eq91416
  have eq91496 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq91417
       grind)
    | exact superpose eq91417 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq91417
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq91417
       grind)
    | exact resolve eq10 eq91417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91575 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1521 y X0
       have i₂ := eq91417
       grind)
    | exact superpose eq91417 eq1521
    | (have j0 := eq1521 X0 x
       grind)
    | exact resolve eq1521 eq91417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521 eq91417
  have eq92129 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq91496 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91496
  have eq92137 : y = (k y x) := by
    first
    | (have i₁ := eq92129
       have i₂ := eq90853
       grind)
    | exact superpose eq90853 eq92129
    | exact resolve eq92129 eq90853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92129
  have eq93654 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j0 := eq91575 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91575
  have eq93664 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq93654
       have i₂ := eq92137
       grind)
    | exact superpose eq92137 eq93654
    | exact resolve eq93654 eq92137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92137 eq93654
  have eq93686 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq93664
       grind)
    | exact superpose eq93664 eq14
    | exact resolve eq14 eq93664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93664
  have eq93695 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq93686
       have i₂ := eq90853
       grind)
    | exact superpose eq90853 eq93686
    | exact resolve eq93686 eq90853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90853 eq93686
  have eq93696 : False := by grind
  exact eq93696

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pyx_pyy_pxy_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq100 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq198 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq195 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq195 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq195 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq195 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq380 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1
       have i₂ := eq198 (σ X1) X0
       grind)
    | (have i₁ := eq26 X0
       have i₂ := eq198 X0 (σ X0)
       grind)
    | exact superpose eq198 eq26
    | (have j1 := eq198 (σ X1) X0
       grind)
    | exact resolve eq26 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4257 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq380 X0 X1
       grind)
    | exact superpose eq380 eq8
    | (have j1 := eq380 X0 X1
       grind)
    | exact resolve eq8 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq9036 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq4257 (σ X0) X1
       grind)
    | exact superpose eq4257 eq13
    | (have j1 := eq4257 (σ X0) X1
       grind)
    | exact resolve eq13 eq4257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4257
  have eq9068 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9036 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq9036
    | (have j0 := eq9036 X0 X1
       grind)
    | exact resolve eq9036 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9036
  have eq9113 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9068 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq9068
    | (have j0 := eq9068 X0 X1
       grind)
    | exact resolve eq9068 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9068
  have eq12868 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq9113 x y
       grind)
    | exact superpose eq9113 eq14
    | (have j1 := eq9113 x y
       grind)
    | exact resolve eq14 eq9113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9113
  have eq13112 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq12868
       have i₂ := eq198 y x
       grind)
    | exact superpose eq198 eq12868
    | (have j1 := eq198 x y
       grind)
    | exact resolve eq12868 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq12868
  have eq13117 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq13112
  have eq13118 : (M.op x x) = (M.op y y) := by grind
  clear eq13117
  have eq13242 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq13118
       grind)
    | exact superpose eq13118 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq13118
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq13118
       grind)
    | exact resolve eq10 eq13118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13275 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq100 y X0
       have i₂ := eq13118
       grind)
    | exact superpose eq13118 eq100
    | (have j0 := eq100 x X0
       grind)
    | exact resolve eq100 eq13118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq13118
  have eq14650 : (M.op x y) = (k x y) := by
    first
    | (have j0 := eq13242 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13242
  have eq27245 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13275 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq13275
    | (have j0 := eq13275 (σ X0)
       grind)
    | (have r₁ := eq13275 (σ x)
       have r₂ := eq26 x
       grind)
    | exact resolve eq13275 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13275
  have eq27269 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq27245 X0
       have i₂ := eq13 X0 y
       grind)
    | exact superpose eq13 eq27245
    | (have j0 := eq27245 X0
       grind)
    | exact resolve eq27245 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27245
  have eq481603 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have j0 := eq27269 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27269
  have eq481605 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq481603
       have i₂ := eq14650
       grind)
    | exact superpose eq14650 eq481603
    | exact resolve eq481603 eq14650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14650 eq481603
  have eq481608 : False := by grind
  exact eq481608

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pyx_pyy_pyx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq68 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq65 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq65 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq65 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq67 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq67 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq67 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq113 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq68 X1 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq68
    | (have j0 := eq68 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq68 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq68 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq68 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq120 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq113 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq123 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq120 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq120 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq120 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq125 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X0 X1
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq123
    | (have j0 := eq123 X0 X1
       grind)
    | exact resolve eq123 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq123
  have eq168 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq70 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq172 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       have j1 := eq125 X1 X0
       grind)
    | (have r₁ := eq168 X1 X0
       have r₂ := eq125 X0 X1
       grind)
    | (have r₁ := eq168 X1 X1
       have r₂ := eq125 X1 X1
       grind)
    | exact resolve eq168 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq168
  have eq195 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq172 (σ X1) (σ X0)
       grind)
    | exact superpose eq172 eq13
    | exact resolve eq13 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq172 X1 X0
       grind)
    | exact superpose eq172 eq195
    | exact resolve eq195 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq195
  have eq704 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq202 x y
       grind)
    | exact superpose eq202 eq14
    | (have r₁ := eq14
       have r₂ := eq202 x y
       grind)
    | exact resolve eq14 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq731 : False := by grind
  exact eq731

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pyx_x_pxy_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (τ X0)
       have i₂ := eq21 (τ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq25 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq25
    | exact resolve eq25 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25
  have eq45 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq54 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq56 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq84 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq54 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq8
    | (have j1 := eq54 X0 X1
       grind)
    | exact resolve eq8 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq207 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq195
    | (have j0 := eq195 X0 X1
       grind)
    | exact resolve eq195 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq1199 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq201 (τ X1) (τ X0)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq201
    | (have j0 := eq201 (τ X0) (τ X1)
       grind)
    | exact resolve eq201 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq201
  have eq1208 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1199 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq1199
    | (have j0 := eq1199 X0 X1
       grind)
    | exact resolve eq1199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1214 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1208 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1208
    | (have j0 := eq1208 X0 X1
       grind)
    | exact resolve eq1208 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1217 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1214 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq1214
    | (have j0 := eq1214 X0 X1
       grind)
    | exact resolve eq1214 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1218 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1217 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq1217
    | (have j0 := eq1217 X0 X1
       grind)
    | exact resolve eq1217 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1217
  have eq1219 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1218 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1218
    | (have j0 := eq1218 X0 X1
       grind)
    | exact resolve eq1218 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1220 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1219 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1219
    | (have j0 := eq1219 X0 X1
       grind)
    | exact resolve eq1219 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1321 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq47
    | exact resolve eq47 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1456 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1321 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1321
    | (have j0 := eq1321 X0 X1
       grind)
    | exact resolve eq1321 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1499 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq84
    | (have j0 := eq84 X1 (σ X0)
       grind)
    | (have r₁ := eq84 X0 (σ X0)
       have r₂ := eq26 X0
       grind)
    | exact resolve eq84 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1521 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1499 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1499
    | (have j0 := eq1499 X0 X1
       grind)
    | exact resolve eq1499 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1566 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq207 x y
       grind)
    | exact superpose eq207 eq14
    | (have j1 := eq207 x y
       grind)
    | exact resolve eq14 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1622 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq41522 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1566
       have i₂ := eq1456 x y
       grind)
    | exact superpose eq1456 eq1566
    | (have j1 := eq1456 x y
       grind)
    | (have r₁ := eq1566
       have r₂ := eq1456 x y
       grind)
    | exact resolve eq1566 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456 eq1566
  have eq41523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq41522
  have eq41524 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq41523
  have eq41646 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq41524
       grind)
    | exact superpose eq41524 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq41524
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq41524
       grind)
    | exact resolve eq11 eq41524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41524
  have eq41647 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq41646
  have eq41649 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41647
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq41647
    | exact resolve eq41647 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41647
  have eq41650 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41649
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq41649
    | exact resolve eq41649 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq41649
  have eq41651 : (σ y) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41650
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq41650
    | exact resolve eq41650 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41650
  have eq90558 : (k y x) = (τ (σ y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq41651
       grind)
    | exact superpose eq41651 eq8
    | exact resolve eq8 eq41651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41651
  have eq90567 : (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (k y x) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq90558
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq90558
    | exact resolve eq90558 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90558
  have eq90570 : (M.op y y) = (τ (σ (M.op x x))) ∨ y = (k y x) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (M.op y y)
       have i₂ := eq90567
       grind)
    | exact superpose eq90567 eq8
    | exact resolve eq8 eq90567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90567
  have eq90579 : (M.op x x) = (M.op y y) ∨ y = (k y x) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq90570
       have i₂ := eq8 (M.op x x)
       grind)
    | exact superpose eq8 eq90570
    | exact resolve eq90570 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90570
  have eq90580 : y = (k y x) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq90579
  have eq90594 : y ≠ y ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1220 y x
       have i₂ := eq90580
       grind)
    | exact superpose eq90580 eq1220
    | (have j0 := eq1220 x y
       grind)
    | (have r₁ := eq1220 y x
       have r₂ := eq90580
       grind)
    | exact resolve eq1220 eq90580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq90580
  have eq90730 : y ≠ y ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq90594
  have eq90731 : (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq90730
  have eq90812 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq90731
       grind)
    | exact superpose eq90731 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq90731
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq90731
       grind)
    | exact resolve eq10 eq90731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90863 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1521 X0 y
       have i₂ := eq90731
       grind)
    | exact superpose eq90731 eq1521
    | (have j0 := eq1521 X0 x
       grind)
    | exact resolve eq1521 eq90731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90731
  have eq91818 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq90812 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90812
  have eq92684 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq90863 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90863
  have eq92706 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq92684
       grind)
    | exact superpose eq92684 eq14
    | exact resolve eq14 eq92684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92684
  have eq92756 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq92706
       have i₂ := eq91818
       grind)
    | exact superpose eq91818 eq92706
    | exact resolve eq92706 eq91818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91818 eq92706
  have eq92771 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq92756
  have eq92772 : y = (M.op x y) := by grind
  clear eq92771
  have eq92776 : y ≠ y ∨ (M.op x x) = (M.op y y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq92772
       grind)
    | exact superpose eq92772 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq92772
       grind)
    | exact resolve eq11 eq92772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92783 : y = (k y x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq92776
  have eq92958 : (σ y) ≠ (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1622 x y
       have i₂ := eq92783
       grind)
    | exact superpose eq92783 eq1622
    | (have j0 := eq1622 x y
       grind)
    | exact resolve eq1622 eq92783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622 eq92783
  have eq93303 : (σ y) ≠ (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq92958
  have eq93304 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq93303
  have eq93405 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq93304
       grind)
    | exact superpose eq93304 eq14
    | exact resolve eq14 eq93304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93304
  have eq93411 : (σ y) ≠ (σ y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq93405
       have i₂ := eq92772
       grind)
    | exact superpose eq92772 eq93405
    | exact resolve eq93405 eq92772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93405
  have eq93412 : (M.op x x) = (M.op y y) := by grind
  clear eq93411
  have eq93520 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq93412
       grind)
    | exact superpose eq93412 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq93412
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq93412
       grind)
    | exact resolve eq10 eq93412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93599 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1521 X0 y
       have i₂ := eq93412
       grind)
    | exact superpose eq93412 eq1521
    | (have j0 := eq1521 X0 x
       grind)
    | exact resolve eq1521 eq93412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521 eq93412
  have eq94620 : (M.op x y) = (k x y) := by
    first
    | (have j0 := eq93520 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93520
  have eq94628 : y = (k x y) := by
    first
    | (have i₁ := eq94620
       have i₂ := eq92772
       grind)
    | exact superpose eq92772 eq94620
    | exact resolve eq94620 eq92772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94620
  have eq96047 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have j0 := eq93599 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93599
  have eq96057 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq96047
       have i₂ := eq94628
       grind)
    | exact superpose eq94628 eq96047
    | exact resolve eq96047 eq94628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94628 eq96047
  have eq96078 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq96057
       grind)
    | exact superpose eq96057 eq14
    | exact resolve eq14 eq96057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96057
  have eq96087 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq96078
       have i₂ := eq92772
       grind)
    | exact superpose eq92772 eq96078
    | exact resolve eq96078 eq92772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92772 eq96078
  have eq96088 : False := by grind
  exact eq96088

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pyx_x_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq43 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X2 X1) = X1 ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq12 X1 X2
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2
       have i₂ := eq12 X0 X2
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X1) = X1 ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X1 X1 X2
       have j1 := eq50 X1 X1 X2
       grind)
    | (have r₁ := eq43 X0 X1 X2
       have r₂ := eq50 X0 X1 X2
       grind)
    | (have r₁ := eq43 X1 X0 X2
       have r₂ := eq50 X0 X1 X2
       grind)
    | (have r₁ := eq43 X0 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq50 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq43 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq50
  have eq97 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq115 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq249 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq116 (σ X1) (σ X0)
       grind)
    | exact superpose eq116 eq13
    | (have j1 := eq116 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq116 X1 (τ X0)
       grind)
    | exact superpose eq116 eq16
    | (have j1 := eq116 X1 (τ X0)
       grind)
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq116
  have eq1627 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq254 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq254
    | exact resolve eq254 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1699 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1627 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1627
    | (have j0 := eq1627 X0 X1
       grind)
    | exact resolve eq1627 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627
  have eq2098 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq97
    | (have j0 := eq97 X1 (σ X0)
       grind)
    | (have r₁ := eq97 X0 (σ X0)
       have r₂ := eq26 X0
       grind)
    | exact resolve eq97 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq2128 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2098 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2098
    | (have j0 := eq2098 X0 X1
       grind)
    | exact resolve eq2098 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098
  have eq2978 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq249 x y
       grind)
    | exact superpose eq249 eq14
    | (have j1 := eq249 x y
       grind)
    | exact resolve eq14 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3008 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq4474 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2978
       have i₂ := eq1699 x y
       grind)
    | exact superpose eq1699 eq2978
    | (have j1 := eq1699 (σ x) (σ y)
       grind)
    | (have r₁ := eq2978
       have r₂ := eq1699 x y
       grind)
    | exact resolve eq2978 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2978
  have eq4475 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4474
  have eq4680 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4475
       grind)
    | exact superpose eq4475 eq14
    | exact resolve eq14 eq4475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4681 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq4475
       grind)
    | exact superpose eq4475 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq4475
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq4475
       grind)
    | exact resolve eq11 eq4475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4475
  have eq4682 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq4681
  have eq4683 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4682
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq4682
    | exact resolve eq4682 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4682
  have eq4688 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4683
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq4683
    | exact resolve eq4683 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4683
  have eq4689 : (σ y) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4688
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq4688
    | exact resolve eq4688 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4688
  have eq50221 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1699 x y
       have i₂ := eq4689
       grind)
    | exact superpose eq4689 eq1699
    | (have j0 := eq1699 x y
       grind)
    | exact resolve eq1699 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4689
  have eq50264 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq50221
  have eq50288 : (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq50264
       have r₂ := eq4680
       grind)
    | exact resolve eq50264 eq4680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4680 eq50264
  have eq51075 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2128 y X0
       have i₂ := eq50288
       grind)
    | exact superpose eq50288 eq2128
    | (have j0 := eq2128 X0 x
       grind)
    | (have r₁ := eq2128 x y
       have r₂ := eq50288
       grind)
    | (have r₁ := eq2128 y x
       have r₂ := eq50288
       grind)
    | exact resolve eq2128 eq50288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2128 eq50288
  have eq123740 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq51075 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51075
  have eq123750 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq123740
       grind)
    | exact superpose eq123740 eq14
    | exact resolve eq14 eq123740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123740
  have eq123792 : y = (M.op x y) := by
    first
    | (have j1 := eq1699 x y
       grind)
    | (have r₁ := eq123750
       have r₂ := eq1699 x y
       grind)
    | exact resolve eq123750 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699 eq123750
  have eq123793 : y ≠ y ∨ (M.op x x) = (M.op y y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq123792
       grind)
    | exact superpose eq123792 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq123792
       grind)
    | exact resolve eq11 eq123792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123794 : y = (k y x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq123793
  have eq123925 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq3008 x y
       have i₂ := eq123794
       grind)
    | exact superpose eq123794 eq3008
    | (have j0 := eq3008 x y
       grind)
    | exact resolve eq3008 eq123794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123794
  have eq124014 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq123925
  have eq124026 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq124014
       grind)
    | exact superpose eq124014 eq14
    | exact resolve eq14 eq124014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124014
  have eq124027 : (σ y) ≠ (σ y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq124026
       have i₂ := eq123792
       grind)
    | exact superpose eq123792 eq124026
    | exact resolve eq124026 eq123792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124026
  have eq124028 : (M.op x x) = (M.op y y) := by grind
  clear eq124027
  have eq124040 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq124028
       grind)
    | exact superpose eq124028 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq124028
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq124028
       grind)
    | exact resolve eq10 eq124028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124028
  have eq124187 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq124040 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124040
  have eq124190 : y = (k y x) := by
    first
    | (have i₁ := eq124187
       have i₂ := eq123792
       grind)
    | exact superpose eq123792 eq124187
    | exact resolve eq124187 eq123792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124187
  have eq124240 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3008 x y
       have i₂ := eq124190
       grind)
    | exact superpose eq124190 eq3008
    | (have j0 := eq3008 x y
       grind)
    | exact resolve eq3008 eq124190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3008 eq124190
  have eq124341 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq124240
  have eq124372 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq124341
       grind)
    | exact superpose eq124341 eq14
    | exact resolve eq14 eq124341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124341
  have eq124376 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq124372
       have i₂ := eq123792
       grind)
    | exact superpose eq123792 eq124372
    | exact resolve eq124372 eq123792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123792 eq124372
  have eq124377 : False := by grind
  exact eq124377

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pyx_y_pxy_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (τ X0)
       have i₂ := eq21 (τ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq25
    | exact resolve eq25 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25
  have eq45 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq54 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq56 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq84 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq54 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq8
    | (have j1 := eq54 X0 X1
       grind)
    | exact resolve eq8 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq207 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq195
    | (have j0 := eq195 X0 X1
       grind)
    | exact resolve eq195 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq1199 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq201 (τ X1) (τ X0)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq201
    | (have j0 := eq201 (τ X0) (τ X1)
       grind)
    | exact resolve eq201 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq201
  have eq1208 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1199 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq1199
    | (have j0 := eq1199 X0 X1
       grind)
    | exact resolve eq1199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1214 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1208 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1208
    | (have j0 := eq1208 X0 X1
       grind)
    | exact resolve eq1208 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1217 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1214 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq1214
    | (have j0 := eq1214 X0 X1
       grind)
    | exact resolve eq1214 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1218 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1217 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq1217
    | (have j0 := eq1217 X0 X1
       grind)
    | exact resolve eq1217 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1217
  have eq1219 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1218 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1218
    | (have j0 := eq1218 X0 X1
       grind)
    | exact resolve eq1218 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1220 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1219 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1219
    | (have j0 := eq1219 X0 X1
       grind)
    | exact resolve eq1219 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1321 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq46
    | exact resolve eq46 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1456 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1321 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1321
    | (have j0 := eq1321 X0 X1
       grind)
    | exact resolve eq1321 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1499 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq84
    | (have j0 := eq84 X1 (σ X0)
       grind)
    | (have r₁ := eq84 X0 (σ X0)
       have r₂ := eq26 X0
       grind)
    | exact resolve eq84 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1521 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1499 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1499
    | (have j0 := eq1499 X0 X1
       grind)
    | exact resolve eq1499 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1566 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq207 x y
       grind)
    | exact superpose eq207 eq14
    | (have j1 := eq207 x y
       grind)
    | exact resolve eq14 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1622 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq37737 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1566
       have i₂ := eq1456 y x
       grind)
    | exact superpose eq1456 eq1566
    | (have j1 := eq1456 x y
       grind)
    | (have r₁ := eq1566
       have r₂ := eq1456 y x
       grind)
    | exact resolve eq1566 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456 eq1566
  have eq37738 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq37737
  have eq37739 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq37738
  have eq37861 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq37739
       grind)
    | exact superpose eq37739 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq37739
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq37739
       grind)
    | exact resolve eq11 eq37739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37739
  have eq37862 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq37861
  have eq37864 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37862
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq37862
    | exact resolve eq37862 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37862
  have eq37865 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37864
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq37864
    | exact resolve eq37864 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq37864
  have eq37866 : (σ x) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37865
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq37865
    | exact resolve eq37865 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37865
  have eq86048 : (k y x) = (τ (σ x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq37866
       grind)
    | exact superpose eq37866 eq8
    | exact resolve eq8 eq37866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37866
  have eq86057 : (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (k y x) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86048
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq86048
    | exact resolve eq86048 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86048
  have eq86058 : (M.op y y) = (τ (σ (M.op x x))) ∨ x = (k y x) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (M.op y y)
       have i₂ := eq86057
       grind)
    | exact superpose eq86057 eq8
    | exact resolve eq8 eq86057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86057
  have eq86067 : (M.op x x) = (M.op y y) ∨ x = (k y x) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86058
       have i₂ := eq8 (M.op x x)
       grind)
    | exact superpose eq8 eq86058
    | exact resolve eq86058 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86058
  have eq86068 : x = (k y x) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq86067
  have eq86078 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1220 y x
       have i₂ := eq86068
       grind)
    | exact superpose eq86068 eq1220
    | (have j0 := eq1220 x y
       grind)
    | (have r₁ := eq1220 y x
       have r₂ := eq86068
       grind)
    | exact resolve eq1220 eq86068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq86068
  have eq86204 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq86078
  have eq86205 : (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq86204
  have eq86284 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq86205
       grind)
    | exact superpose eq86205 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq86205
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq86205
       grind)
    | exact resolve eq10 eq86205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86324 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1521 X0 y
       have i₂ := eq86205
       grind)
    | exact superpose eq86205 eq1521
    | (have j0 := eq1521 X0 x
       grind)
    | exact resolve eq1521 eq86205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86205
  have eq87271 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq86284 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86284
  have eq88115 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq86324 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86324
  have eq88135 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq88115
       grind)
    | exact superpose eq88115 eq14
    | exact resolve eq14 eq88115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88115
  have eq88160 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88135
       have i₂ := eq87271
       grind)
    | exact superpose eq87271 eq88135
    | exact resolve eq88135 eq87271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87271 eq88135
  have eq88175 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq88160
  have eq88176 : x = (M.op x y) := by grind
  clear eq88175
  have eq88180 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq88176
       grind)
    | exact superpose eq88176 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq88176
       grind)
    | exact resolve eq11 eq88176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88187 : x = (k y x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq88180
  have eq88356 : (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1622 x y
       have i₂ := eq88187
       grind)
    | exact superpose eq88187 eq1622
    | (have j0 := eq1622 x y
       grind)
    | exact resolve eq1622 eq88187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622 eq88187
  have eq88693 : (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq88356
  have eq88694 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq88693
  have eq88801 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq88694
       grind)
    | exact superpose eq88694 eq14
    | exact resolve eq14 eq88694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88694
  have eq88807 : (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq88801
       have i₂ := eq88176
       grind)
    | exact superpose eq88176 eq88801
    | exact resolve eq88801 eq88176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88801
  have eq88808 : (M.op x x) = (M.op y y) := by grind
  clear eq88807
  have eq88908 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq88808
       grind)
    | exact superpose eq88808 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq88808
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq88808
       grind)
    | exact resolve eq10 eq88808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88987 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1521 X0 y
       have i₂ := eq88808
       grind)
    | exact superpose eq88808 eq1521
    | (have j0 := eq1521 X0 x
       grind)
    | exact resolve eq1521 eq88808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521 eq88808
  have eq89990 : (M.op x y) = (k x y) := by
    first
    | (have j0 := eq88908 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88908
  have eq89998 : x = (k x y) := by
    first
    | (have i₁ := eq89990
       have i₂ := eq88176
       grind)
    | exact superpose eq88176 eq89990
    | exact resolve eq89990 eq88176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89990
  have eq91322 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have j0 := eq88987 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88987
  have eq91332 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq91322
       have i₂ := eq89998
       grind)
    | exact superpose eq89998 eq91322
    | exact resolve eq91322 eq89998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89998 eq91322
  have eq91353 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq91332
       grind)
    | exact superpose eq91332 eq14
    | exact resolve eq14 eq91332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91332
  have eq91362 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq91353
       have i₂ := eq88176
       grind)
    | exact superpose eq88176 eq91353
    | exact resolve eq91353 eq88176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88176 eq91353
  have eq91363 : False := by grind
  exact eq91363

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pyx_y_pyx_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq43 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X2 X1) = X2 ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq12 X1 X2
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2
       have i₂ := eq12 X0 X2
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X1) = X2 ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X1 X1 X2
       have j1 := eq50 X1 X1 X2
       grind)
    | (have r₁ := eq43 X0 X1 X2
       have r₂ := eq50 X0 X1 X2
       grind)
    | (have r₁ := eq43 X1 X0 X2
       have r₂ := eq50 X0 X1 X2
       grind)
    | (have r₁ := eq43 X0 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq50 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq43 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq50
  have eq97 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq115 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq249 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq116 (σ X1) (σ X0)
       grind)
    | exact superpose eq116 eq13
    | (have j1 := eq116 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq116 (τ X1) X0
       grind)
    | exact superpose eq116 eq15
    | (have j1 := eq116 (τ X1) X0
       grind)
    | exact resolve eq15 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq116
  have eq1625 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq251 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq251
    | exact resolve eq251 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq1697 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1625 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1625
    | (have j0 := eq1625 X0 X1
       grind)
    | exact resolve eq1625 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq2096 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq97
    | (have j0 := eq97 X1 (σ X0)
       grind)
    | (have r₁ := eq97 X0 (σ X0)
       have r₂ := eq26 X0
       grind)
    | exact resolve eq97 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq2126 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2096 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2096
    | (have j0 := eq2096 X0 X1
       grind)
    | exact resolve eq2096 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096
  have eq2975 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq249 x y
       grind)
    | exact superpose eq249 eq14
    | (have j1 := eq249 x y
       grind)
    | exact resolve eq14 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3005 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq4474 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2975
       have i₂ := eq1697 y x
       grind)
    | exact superpose eq1697 eq2975
    | (have j1 := eq1697 (σ y) (σ x)
       grind)
    | (have r₁ := eq2975
       have r₂ := eq1697 y x
       grind)
    | exact resolve eq2975 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2975
  have eq4475 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4474
  have eq4676 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4475
       grind)
    | exact superpose eq4475 eq14
    | exact resolve eq14 eq4475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4677 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq4475
       grind)
    | exact superpose eq4475 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq4475
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq4475
       grind)
    | exact resolve eq11 eq4475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4475
  have eq4678 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4677
  have eq4679 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4678
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq4678
    | exact resolve eq4678 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4678
  have eq4684 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4679
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq4679
    | exact resolve eq4679 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4679
  have eq4685 : (σ x) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4684
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq4684
    | exact resolve eq4684 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4684
  have eq48903 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1697 y x
       have i₂ := eq4685
       grind)
    | exact superpose eq4685 eq1697
    | (have j0 := eq1697 y x
       grind)
    | exact resolve eq1697 eq4685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4685
  have eq48946 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq48903
  have eq48970 : (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq48946
       have r₂ := eq4676
       grind)
    | exact resolve eq48946 eq4676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4676 eq48946
  have eq49860 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2126 y X0
       have i₂ := eq48970
       grind)
    | exact superpose eq48970 eq2126
    | (have j0 := eq2126 X0 x
       grind)
    | (have r₁ := eq2126 x y
       have r₂ := eq48970
       grind)
    | (have r₁ := eq2126 y x
       have r₂ := eq48970
       grind)
    | exact resolve eq2126 eq48970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126 eq48970
  have eq123001 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq49860 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49860
  have eq123011 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq123001
       grind)
    | exact superpose eq123001 eq14
    | exact resolve eq14 eq123001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123001
  have eq123053 : x = (M.op x y) := by
    first
    | (have j1 := eq1697 y x
       grind)
    | (have r₁ := eq123011
       have r₂ := eq1697 y x
       grind)
    | exact resolve eq123011 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697 eq123011
  have eq123054 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq123053
       grind)
    | exact superpose eq123053 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq123053
       grind)
    | exact resolve eq11 eq123053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123055 : x = (k y x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq123054
  have eq123186 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq3005 x y
       have i₂ := eq123055
       grind)
    | exact superpose eq123055 eq3005
    | (have j0 := eq3005 x y
       grind)
    | exact resolve eq3005 eq123055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123055
  have eq123275 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq123186
  have eq123287 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq123275
       grind)
    | exact superpose eq123275 eq14
    | exact resolve eq14 eq123275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123275
  have eq123288 : (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq123287
       have i₂ := eq123053
       grind)
    | exact superpose eq123053 eq123287
    | exact resolve eq123287 eq123053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123287
  have eq123289 : (M.op x x) = (M.op y y) := by grind
  clear eq123288
  have eq123301 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq123289
       grind)
    | exact superpose eq123289 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq123289
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq123289
       grind)
    | exact resolve eq10 eq123289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123289
  have eq123447 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq123301 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123301
  have eq123450 : x = (k y x) := by
    first
    | (have i₁ := eq123447
       have i₂ := eq123053
       grind)
    | exact superpose eq123053 eq123447
    | exact resolve eq123447 eq123053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123447
  have eq123500 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3005 x y
       have i₂ := eq123450
       grind)
    | exact superpose eq123450 eq3005
    | (have j0 := eq3005 x y
       grind)
    | exact resolve eq3005 eq123450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3005 eq123450
  have eq123601 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq123500
  have eq123632 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq123601
       grind)
    | exact superpose eq123601 eq14
    | exact resolve eq14 eq123601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123601
  have eq123636 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq123632
       have i₂ := eq123053
       grind)
    | exact superpose eq123053 eq123632
    | exact resolve eq123632 eq123053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123053 eq123632
  have eq123637 : False := by grind
  exact eq123637
