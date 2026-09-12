import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pxy_pyy_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
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
  clear eq25 eq36
  have eq52 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    grind
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq88
    | exact resolve eq88 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq265 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq379 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X0) X1 x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq493 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X0
       have i₂ := eq379 X0 (σ X0)
       grind)
    | (have i₁ := eq73 X0 X0
       have i₂ := eq379 (σ X0) X1
       grind)
    | exact superpose eq379 eq73
    | exact resolve eq73 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq520 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq493 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq538 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq265 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq265
    | exact resolve eq265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq12413 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq520 X0 (τ X1)
       grind)
    | exact superpose eq520 eq35
    | (have j1 := eq520 X0 (τ X1)
       grind)
    | exact resolve eq35 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq520
  have eq12500 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12413 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq12413
    | (have j0 := eq12413 X0 X1
       grind)
    | exact resolve eq12413 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12413
  have eq12522 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12500 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq12500
    | (have j0 := eq12500 X0 X1
       grind)
    | exact resolve eq12500 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12500
  have eq13149 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12522 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12522
  have eq13223 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13149 X1 (τ X0)
       have i₂ := eq538 X0 X0
       grind)
    | exact superpose eq538 eq13149
    | (have j0 := eq13149 X1 (τ X0)
       grind)
    | exact resolve eq13149 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq18807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq18808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18807
    | exact resolve eq18807 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18807
  have eq18819 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18808
       have r₂ := eq28
       grind)
    | exact resolve eq18808 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18808
  have eq18821 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq18819
       have i₂ := eq379 X0 sF3
       grind)
    | (have i₁ := eq18819
       have i₂ := eq379 sF3 x
       grind)
    | exact superpose eq379 eq18819
    | exact resolve eq18819 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18819
  have eq18930 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq18821 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18821
  have eq18931 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq18930
  have eq18939 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq18931
       have i₂ := eq379 X0 sF2
       grind)
    | (have i₁ := eq18931
       have i₂ := eq379 sF2 x
       grind)
    | exact superpose eq379 eq18931
    | exact resolve eq18931 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18931
  have eq18996 : ∀ X0 X1 : G, x = (M.op x x) ∨ (M.op X0 X0) = x ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq18939 X1
       have i₂ := eq379 X0 y
       grind)
    | (have i₁ := eq18939 X1
       have i₂ := eq379 y X0
       grind)
    | exact superpose eq379 eq18939
    | (have j0 := eq18939 X1
       grind)
    | exact resolve eq18939 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq18939
  have eq19368 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq18996 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18996
  have eq19370 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq19368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19368
  have eq19385 : ∀ X0 : G, (k x x) = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    grind
  have eq19856 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq19385 X0
       grind)
    | exact superpose eq19385 eq44
    | (have j1 := eq19385 X0
       grind)
    | exact resolve eq44 eq19385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq19385
  have eq21434 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq19856 X0
       have i₂ := eq19370 X1
       grind)
    | exact superpose eq19370 eq19856
    | (have j0 := eq19856 X0
       have j1 := eq19370 X0
       grind)
    | exact resolve eq19856 eq19370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19370 eq19856
  have eq21543 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq21434 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21434
    | (have j0 := eq21434 X0 X0
       grind)
    | exact resolve eq21434 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21434
  have eq21545 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq21543 X1 X1
       have j1 := eq13149 X1 (σ x)
       grind)
    | (have r₁ := eq21543 X0 X1
       have r₂ := eq13149 X0 (σ x)
       grind)
    | exact resolve eq21543 eq13149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13149 eq21543
  have eq21670 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq21545 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21545
  have eq21671 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq21670 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21670
  have eq21721 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    grind
  have eq21725 : (k (σ x) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq63 x
       have i₂ := eq21671 x
       grind)
    | exact superpose eq21671 eq63
    | exact resolve eq63 eq21671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq21875 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21725
       have i₂ := eq21671 sF2
       grind)
    | exact superpose eq21671 eq21725
    | exact resolve eq21725 eq21671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21725
  have eq21928 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq21875
       have i₂ := eq21671 sF2
       grind)
    | exact superpose eq21671 eq21875
    | exact resolve eq21875 eq21671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21875
  have eq21994 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | exact superpose eq21928 eq13223
    | (have j0 := eq13223 (σ x) X0
       grind)
    | exact resolve eq13223 eq21928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13223 eq21928
  have eq21997 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | (have j0 := eq21994 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21994
  have eq22013 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq29 eq21997
    | exact resolve eq21997 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21997
  have eq22034 : x = (σ x) := by
    first
    | (have i₁ := eq22013 x
       have i₂ := eq21671 x
       grind)
    | exact superpose eq21671 eq22013
    | exact resolve eq22013 eq21671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21671 eq22013
  have eq22044 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq22034 eq27
    | exact resolve eq27 eq22034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq22369 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq22034 eq21721
    | exact resolve eq21721 eq22034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21721
  have eq22796 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq22369 y
       grind)
    | exact superpose eq22369 eq45
    | exact resolve eq45 eq22369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq22834 : (σ (M.op x y)) = (k x (σ y)) := by
    first
    | exact superpose eq22034 eq22796
    | exact resolve eq22796 eq22034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22034 eq22796
  have eq22914 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq22834
       have i₂ := eq22369 sF3
       grind)
    | exact superpose eq22369 eq22834
    | exact resolve eq22834 eq22369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22369 eq22834
  have eq22985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22044 eq22914
    | exact resolve eq22914 eq22044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22044 eq22914
  have eq23032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22985
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22985
    | exact resolve eq22985 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq22985
  have eq23065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq23032
    | exact resolve eq23032 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23032
  have eq23086 : False := by grind
  exact eq23086

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pyx_y_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    grind
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq14 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq14 eq63
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq23
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq106 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq108
    | exact resolve eq108 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq380 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X0) X1 x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) (M.op X4 X4)) = X3 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq14 X3 x X4
       have i₂ := eq52 X0 x X1
       grind)
    | (have i₁ := eq14 X0 (M.op x x) x
       have i₂ := eq52 x X1 x
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 ∨ (k X1 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq380 X0 X1
       grind)
    | (have i₁ := eq12 X1 X2
       have i₂ := eq380 X1 X0
       grind)
    | exact superpose eq380 eq12
    | (have j0 := eq12 X1 X2
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq380 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq380 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq433 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1
       have i₂ := eq52 X1 X0 X1
       grind)
    | (have i₁ := eq64 X0
       have i₂ := eq52 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq52 eq64
    | exact resolve eq64 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq497 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (σ (k X2 X2)) ∨ (σ X2) = (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (σ X2) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 X1 X1
       have i₂ := eq52 X0 (σ X1) X2
       grind)
    | exact superpose eq52 eq90
    | exact resolve eq90 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq90
  have eq522 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (σ (k X2 X2)) ∨ (σ X2) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq497 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq5916 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) ∨ (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq522 X1 X2 (M.op X0 X0)
       have i₂ := eq433 X0 X0
       grind)
    | exact superpose eq433 eq522
    | (have j0 := eq522 X1 X2 (M.op X0 X0)
       grind)
    | exact resolve eq522 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq522
  have eq6015 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq5916 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5916
  have eq6098 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6015 X2 (M.op X0 X0) x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq6015
    | exact resolve eq6015 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6143 : ∀ X0 X3 X4 : G, (M.op (M.op (σ (M.op X0 X0)) X3) (M.op X4 X4)) = X3 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq384 x x X3 X4
       have i₂ := eq6015 X0 x x
       grind)
    | exact superpose eq6015 eq384
    | exact resolve eq384 eq6015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq6015
  have eq6372 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1)
       have i₂ := eq6098 X0 X1
       grind)
    | exact superpose eq6098 eq16
    | exact resolve eq16 eq6098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6376 : ∀ X0 X1 : G, (σ (k (M.op X1 X1) x)) = (k (M.op X0 X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (M.op X1 X1)
       have i₂ := eq6098 X0 X1
       grind)
    | exact superpose eq6098 eq40
    | exact resolve eq40 eq6098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq6098
  have eq6407 : ∀ X0 X1 : G, (σ (k (M.op X1 X1) x)) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6376 X0 X1
       have i₂ := eq410 X0 sF2
       grind)
    | exact superpose eq410 eq6376
    | exact resolve eq6376 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6376
  have eq6421 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X0)) = (σ (M.op x (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6407 X0 X1
       have i₂ := eq410 X1 x
       grind)
    | exact superpose eq410 eq6407
    | exact resolve eq6407 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq6407
  have eq14776 : (τ (k (σ y) (σ y))) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq16
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq14845 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq84 eq14776
    | exact resolve eq14776 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq14776
  have eq34733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq34734 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq34733
    | exact resolve eq34733 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34733
  have eq34745 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq34734
       have r₂ := eq28
       grind)
    | exact resolve eq34734 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34734
  have eq34747 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq34745
       have i₂ := eq380 X0 sF3
       grind)
    | (have i₁ := eq34745
       have i₂ := eq380 sF3 x
       grind)
    | exact superpose eq380 eq34745
    | exact resolve eq34745 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34745
  have eq35035 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq34747 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34747
  have eq35036 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq35035
  have eq35177 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq35036 eq6372
    | exact resolve eq6372 eq35036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6372 eq35036
  have eq35272 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 X0) = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30 eq35177
    | exact resolve eq35177 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq35177
  have eq35761 : ∀ X0 X1 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (k y X0) = X0 ∨ (M.op X1 X1) = y ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq35272 X1
       grind)
    | exact superpose eq35272 eq12
    | (have j0 := eq12 y X0
       have j1 := eq35272 X0
       grind)
    | (have r₁ := eq12 y X1
       have r₂ := eq35272 X0
       grind)
    | (have r₁ := eq12 y X1
       have r₂ := eq35272 y
       grind)
    | exact resolve eq12 eq35272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35272
  have eq35893 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ (k y X0) = X0 ∨ (M.op X1 X1) = y ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq35761 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35761
  have eq35921 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ (k y X0) = X0 ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have j0 := eq35893 X0 X0
       have j1 := eq407 X0 y X0
       grind)
    | (have r₁ := eq35893 X0 X1
       have r₂ := eq407 X0 y x
       grind)
    | (have r₁ := eq35893 (M.op X0 X0) X1
       have r₂ := eq407 X0 (k y (M.op X0 X0)) x
       grind)
    | (have r₁ := eq35893 X0 X0
       have r₂ := eq407 X0 y x
       grind)
    | exact resolve eq35893 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35893
  have eq35923 : ∀ X0 : G, (k y X0) = X0 ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq35921 X0 X0
       have j1 := eq407 X0 y X0
       grind)
    | (have r₁ := eq35921 X0 x
       have r₂ := eq407 X0 y x
       grind)
    | (have r₁ := eq35921 (M.op X0 X0) x
       have r₂ := eq407 X0 (k y (M.op X0 X0)) x
       grind)
    | (have r₁ := eq35921 X0 X0
       have r₂ := eq407 X0 y x
       grind)
    | exact resolve eq35921 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq35921
  have eq36163 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14845
       have i₂ := eq35923 y
       grind)
    | exact superpose eq35923 eq14845
    | (have j1 := eq35923 y
       grind)
    | exact resolve eq14845 eq35923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14845 eq35923
  have eq36175 : y = (M.op y y) := by grind
  clear eq36163
  have eq36620 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq36175
       have i₂ := eq380 X0 y
       grind)
    | (have i₁ := eq36175
       have i₂ := eq380 y X0
       grind)
    | exact superpose eq380 eq36175
    | exact resolve eq36175 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq36175
  have eq36923 : ∀ X1 : G, (σ (M.op x (M.op X1 X1))) = (M.op (σ x) y) := by
    intro X1
    first
    | (have i₁ := eq6421 x X1
       have i₂ := eq36620 x
       grind)
    | exact superpose eq36620 eq6421
    | exact resolve eq6421 eq36620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6421
  have eq37051 : ∀ X0 : G, y = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6143 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq36620 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq36620 eq6143
    | exact resolve eq6143 eq36620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6143
  have eq37090 : y = (σ y) := by
    first
    | (have i₁ := eq37051 x
       have i₂ := eq36620 x
       grind)
    | exact superpose eq36620 eq37051
    | exact resolve eq37051 eq36620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37051
  have eq37179 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq36923 x
       have i₂ := eq36620 x
       grind)
    | exact superpose eq36620 eq36923
    | exact resolve eq36923 eq36620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36620 eq36923
  have eq37305 : y = (σ y) := by
    first
    | (have i₁ := eq37090
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37090
    | exact resolve eq37090 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq37090
  have eq37353 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq37179
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37179
    | exact resolve eq37179 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq37179
  have eq37425 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq21 eq37353
    | exact resolve eq37353 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq37353
  have eq37460 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq37305 eq27
    | exact resolve eq27 eq37305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq37305
  have eq39005 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37425 eq37460
    | exact resolve eq37460 eq37425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37425 eq37460
  have eq39006 : False := by grind
  exact eq39006

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
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
  clear eq25 eq36
  have eq52 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    grind
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86
    | exact resolve eq86 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X0) X1 x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq406 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  have eq430 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq108 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq108
    | (have j0 := eq108 (σ X0)
       grind)
    | exact resolve eq108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq3740 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq430 X0
       have i₂ := eq373 X0 (σ X0)
       grind)
    | (have i₁ := eq430 X0
       have i₂ := eq373 (σ X0) X1
       grind)
    | exact superpose eq373 eq430
    | exact resolve eq430 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq17387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17387
    | exact resolve eq17387 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17387
  have eq17399 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17388
       have r₂ := eq28
       grind)
    | exact resolve eq17388 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17388
  have eq17401 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17399
    | exact resolve eq17399 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17399
  have eq17403 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17401 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq17401
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq17401
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17401
       grind)
    | exact resolve eq12 eq17401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17401
  have eq17405 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq17403
  have eq17407 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17405
       have r₂ := eq27
       grind)
    | exact resolve eq17405 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17405
  have eq17414 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17407 eq87
    | exact resolve eq87 eq17407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17407
  have eq17423 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq17414
  have eq17426 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq17423
       have r₂ := eq28
       grind)
    | exact resolve eq17423 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17423
  have eq17433 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq17426
  have eq17487 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq27 eq17433
    | exact resolve eq17433 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17433
  have eq17873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq17487 eq87
    | exact resolve eq87 eq17487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq17487
  have eq17881 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq17873
  have eq17883 : (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17881
       have r₂ := eq28
       grind)
    | exact resolve eq17881 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17881
  have eq17885 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq17883
       grind)
    | exact superpose eq17883 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17883
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq17883
       grind)
    | exact resolve eq12 eq17883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17883
  have eq17887 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq17885
  have eq17889 : (M.op x y) = (k x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17887
       have r₂ := eq19
       grind)
    | exact resolve eq17887 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17887
  have eq18170 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq17889
       grind)
    | exact superpose eq17889 eq45
    | exact resolve eq45 eq17889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17889
  have eq18190 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq18170
    | exact resolve eq18170 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18170
  have eq18205 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18190 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq18190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18205
    | exact resolve eq18205 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18205
  have eq18221 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18210
       have r₂ := eq28
       grind)
    | exact resolve eq18210 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18210
  have eq18223 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18221
    | exact resolve eq18221 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18221
  have eq18911 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18223 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq18223
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq18223
       grind)
    | exact resolve eq12 eq18223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18223
  have eq18913 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq18911
  have eq18915 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18913
       have r₂ := eq27
       grind)
    | exact resolve eq18913 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18913
  have eq18936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18915 eq18190
    | exact resolve eq18190 eq18915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18915
  have eq18939 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq18936
  have eq18950 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18939
       have r₂ := eq28
       grind)
    | exact resolve eq18939 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18939
  have eq18957 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq18950
  have eq19011 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18957
    | exact resolve eq18957 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18957
  have eq19147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19011 eq18190
    | exact resolve eq18190 eq19011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18190 eq19011
  have eq19149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq19147
  have eq19159 : x = (M.op y y) := by
    first
    | (have r₁ := eq19149
       have r₂ := eq28
       grind)
    | exact resolve eq19149 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19149
  have eq19161 : ∀ X0 : G, x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq19159
       have i₂ := eq373 X0 y
       grind)
    | (have i₁ := eq19159
       have i₂ := eq373 y X0
       grind)
    | exact superpose eq373 eq19159
    | exact resolve eq19159 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq19168 : (M.op x y) = (k x y) := by grind
  have eq19193 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq406 y x
       have i₂ := eq19159
       grind)
    | exact superpose eq19159 eq406
    | exact resolve eq406 eq19159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq19159
  have eq19224 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq19168
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19168
    | exact resolve eq19168 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq19168
  have eq19253 : (k x (M.op x x)) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq63 x
       have i₂ := eq19161 x
       grind)
    | exact superpose eq19161 eq63
    | exact resolve eq63 eq19161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq19391 : (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq19253
       have i₂ := eq19161 x
       grind)
    | exact superpose eq19161 eq19253
    | exact resolve eq19253 eq19161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19253
  have eq19432 : x = (k x x) := by
    first
    | (have i₁ := eq19391
       have i₂ := eq19161 x
       grind)
    | exact superpose eq19161 eq19391
    | exact resolve eq19391 eq19161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19391
  have eq19498 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq19224
       grind)
    | exact superpose eq19224 eq45
    | exact resolve eq45 eq19224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq19224
  have eq19516 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq19498
    | exact resolve eq19498 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq19498
  have eq19536 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ (σ x) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3740 X0 x
       have i₂ := eq19432
       grind)
    | exact superpose eq19432 eq3740
    | (have j0 := eq3740 X0 x
       grind)
    | exact resolve eq3740 eq19432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3740 eq19432
  have eq19540 : ∀ X0 : G, (σ x) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq19536 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19536
  have eq19549 : x = (σ x) := by
    first
    | (have i₁ := eq19540 x
       have i₂ := eq19161 x
       grind)
    | exact superpose eq19161 eq19540
    | exact resolve eq19540 eq19161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19161 eq19540
  have eq19562 : x = (σ x) := by
    first
    | (have i₁ := eq19549
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19549
    | exact resolve eq19549 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq19549
  have eq19564 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq19562 eq27
    | exact resolve eq27 eq19562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq19773 : (σ (M.op x y)) = (k x (σ y)) := by
    first
    | exact superpose eq19562 eq19516
    | exact resolve eq19516 eq19562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19516 eq19562
  have eq20237 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq19773
       have i₂ := eq19193 sF3
       grind)
    | exact superpose eq19193 eq19773
    | exact resolve eq19773 eq19193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19193 eq19773
  have eq20238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19564 eq20237
    | exact resolve eq20237 eq19564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19564 eq20237
  have eq20308 : False := by grind
  exact eq20308

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pxx_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq98 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq91 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq91 X0 (M.op X1 X1)
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq91 X0 X1
       have r₂ := eq12 (k X1 X0) X1
       grind)
    | exact resolve eq91 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq159 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq24 (M.op X0 X0) X1 x
       grind)
    | (have i₁ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq24 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq189 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq159 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq159 X1 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq159
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq159 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq219 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq189 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq189 X0 X1 X1
       have r₂ := eq12 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq189 X1 X1 X2
       have r₂ := eq12 (M.op X2 X2) X1
       grind)
    | (have r₁ := eq189 X1 X1 X2
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | exact resolve eq189 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq375 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq98 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq378 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq375 X0 X1
       have j1 := eq219 X0 X1 x
       grind)
    | (have r₁ := eq375 X1 X1
       have r₂ := eq219 X1 X1 X1
       grind)
    | (have r₁ := eq375 x X1
       have r₂ := eq219 x X1 x
       grind)
    | exact resolve eq375 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq375
  have eq403 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq378 (σ X0) (σ X1)
       grind)
    | exact superpose eq378 eq15
    | exact resolve eq15 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq403 X0 X1
       have i₂ := eq378 X0 X1
       grind)
    | exact superpose eq378 eq403
    | exact resolve eq403 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq403
  have eq2147 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq408 x y
       grind)
    | exact superpose eq408 eq16
    | (have r₁ := eq16
       have r₂ := eq408 x y
       grind)
    | exact resolve eq16 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq2199 : False := by grind
  exact eq2199

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq31 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X1 X1) X2
       have i₂ := eq9 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X1 X2 : G, (M.op X1 X1) = (M.op X2 X2) := by
    intro X1 X2
    first
    | (have i₁ := eq31 X1 (M.op X2 X2) x
       have i₂ := eq9 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq96 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    grind
  clear eq69
  have eq155 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq155 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq162 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq161 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq329 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq162 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq337 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq329 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq329 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq329 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq329 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq329 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq372 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq337 X0 X1
       grind)
    | (have i₁ := eq96 X0 X1
       have i₂ := eq337 (M.op X1 X1) X1
       grind)
    | exact superpose eq337 eq96
    | (have j1 := eq337 X0 X2
       grind)
    | exact resolve eq96 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq337
  have eq626 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq372 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq627 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq626 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq643 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq627 (σ X0) (σ X1)
       grind)
    | exact superpose eq627 eq15
    | exact resolve eq15 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq643 X0 X1
       have i₂ := eq627 X0 X1
       grind)
    | exact superpose eq627 eq643
    | exact resolve eq643 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627 eq643
  have eq1246 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq650 x y
       grind)
    | exact superpose eq650 eq16
    | (have r₁ := eq16
       have r₂ := eq650 x y
       grind)
    | exact resolve eq16 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq1273 : False := by grind
  exact eq1273

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
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
  have eq52 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112
    | exact resolve eq112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq383 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X0) X1 x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq412 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  have eq688 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq10283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq10283
    | exact resolve eq10283 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10283
  have eq10295 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq10284
       have r₂ := eq28
       grind)
    | exact resolve eq10284 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10284
  have eq10297 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq10295
    | exact resolve eq10295 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10295
  have eq10419 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq10297
  have eq10453 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq10419
    | exact resolve eq10419 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10419
  have eq10780 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq10453 eq113
    | exact resolve eq113 eq10453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10453
  have eq10789 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10780
  have eq10791 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10789
       have r₂ := eq28
       grind)
    | exact resolve eq10789 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10789
  have eq10799 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10791
  have eq10834 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10799
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10799
    | exact resolve eq10799 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10799
  have eq11169 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq10834
       grind)
    | exact superpose eq10834 eq45
    | exact resolve eq45 eq10834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10834
  have eq11185 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11169
    | exact resolve eq11169 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11169
  have eq11322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11185 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq11185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11322
    | exact resolve eq11322 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11322
  have eq11336 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11325
       have r₂ := eq28
       grind)
    | exact resolve eq11325 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11325
  have eq11338 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11336
    | exact resolve eq11336 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11336
  have eq11339 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11338
  have eq11347 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11339
  have eq11384 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11347
    | exact resolve eq11347 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11347
  have eq11595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11384 eq11185
    | exact resolve eq11185 eq11384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11185 eq11384
  have eq11598 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11595
  have eq11602 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11598
       have r₂ := eq28
       grind)
    | exact resolve eq11598 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11598
  have eq11604 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11602 eq74
    | (have r₁ := eq74
       have r₂ := eq11602
       grind)
    | exact resolve eq74 eq11602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq11605 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11602 eq28
    | exact resolve eq28 eq11602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11602
  have eq11606 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11604
  have eq11619 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11606 eq113
    | exact resolve eq113 eq11606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11636 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq11619
  have eq11650 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11636
       have r₂ := eq11605
       grind)
    | exact resolve eq11636 eq11605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11636
  have eq11662 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq11650
  have eq11699 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11662
    | exact resolve eq11662 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11662
  have eq11852 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11699 eq113
    | exact resolve eq113 eq11699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq11699
  have eq11865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq11852
  have eq11869 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11865
       have r₂ := eq28
       grind)
    | exact resolve eq11865 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11865
  have eq11880 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq11869
  have eq11919 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11880
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11880
    | exact resolve eq11880 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11880
  have eq12048 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11919
       grind)
    | exact superpose eq11919 eq45
    | exact resolve eq45 eq11919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11919
  have eq12064 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq12048
    | exact resolve eq12048 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12048
  have eq12082 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12064 eq11606
    | exact resolve eq11606 eq12064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11606
  have eq12087 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12082
  have eq12095 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12087
       have r₂ := eq11605
       grind)
    | exact resolve eq12087 eq11605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11605 eq12087
  have eq12117 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12095
  have eq12157 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12117
    | exact resolve eq12117 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12117
  have eq12527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12157 eq12064
    | exact resolve eq12064 eq12157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12064 eq12157
  have eq12530 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12527
  have eq12538 : y = (M.op x y) := by
    first
    | (have r₁ := eq12530
       have r₂ := eq28
       grind)
    | exact resolve eq12530 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12530
  have eq12541 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq12538 eq21
    | exact resolve eq21 eq12538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq12546 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq12538 eq73
    | (have r₁ := eq73
       have r₂ := eq12538
       grind)
    | exact resolve eq73 eq12538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq12594 : y = (k x y) ∨ x = (M.op y y) := by grind
  clear eq12546
  have eq12645 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12541
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12541
    | exact resolve eq12541 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12541
  have eq12646 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq12645 eq27
    | exact resolve eq27 eq12645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq13585 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq12594
       grind)
    | exact superpose eq12594 eq45
    | exact resolve eq45 eq12594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13595 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq688 x y
       have i₂ := eq12594
       grind)
    | exact superpose eq12594 eq688
    | (have j0 := eq688 x y
       grind)
    | exact resolve eq688 eq12594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12594
  have eq13598 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq13595
  have eq13605 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13598
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13598
    | exact resolve eq13598 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13598
  have eq13613 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12645 eq13585
    | exact resolve eq13585 eq12645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13585
  have eq13615 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12645 eq13605
    | exact resolve eq13605 eq12645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13605
  have eq13623 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13613
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13613
    | exact resolve eq13613 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13613
  have eq13624 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13615
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13615
    | exact resolve eq13615 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13615
  have eq13629 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12645 eq13623
    | exact resolve eq13623 eq12645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13623
  have eq13630 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12646 eq13624
    | exact resolve eq13624 eq12646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13624
  have eq13631 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq13630
       have r₂ := eq28
       grind)
    | exact resolve eq13630 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13630
  have eq13632 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13631
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13631
    | exact resolve eq13631 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13631
  have eq13633 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12645 eq13632
    | exact resolve eq13632 eq12645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13632
  have eq13634 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13633
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13633
    | exact resolve eq13633 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13633
  have eq13684 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by grind
  clear eq13634
  have eq13720 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12646 eq13684
    | exact resolve eq13684 eq12646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13684
  have eq13838 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq13720 eq13629
    | exact resolve eq13629 eq13720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13629 eq13720
  have eq13841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq13838
  have eq13843 : x = (M.op y y) := by
    first
    | (have r₁ := eq13841
       have r₂ := eq28
       grind)
    | exact resolve eq13841 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13841
  have eq13856 : ∀ X0 : G, x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13843
       have i₂ := eq383 X0 y
       grind)
    | (have i₁ := eq13843
       have i₂ := eq383 y X0
       grind)
    | exact superpose eq383 eq13843
    | exact resolve eq13843 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq13866 : (M.op x y) = (k x y) := by grind
  have eq13888 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq412 y x
       have i₂ := eq13843
       grind)
    | exact superpose eq13843 eq412
    | exact resolve eq412 eq13843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq13843
  have eq13902 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13866
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13866
    | exact resolve eq13866 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq13866
  have eq13904 : y = (k x y) := by
    first
    | exact superpose eq12538 eq13902
    | exact resolve eq13902 eq12538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12538 eq13902
  have eq14341 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq13904
       grind)
    | exact superpose eq13904 eq45
    | exact resolve eq45 eq13904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq14351 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq688 x y
       have i₂ := eq13904
       grind)
    | exact superpose eq13904 eq688
    | (have j0 := eq688 x y
       grind)
    | exact resolve eq688 eq13904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq13904
  have eq14354 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq14351
  have eq14360 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq14354
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14354
    | exact resolve eq14354 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14354
  have eq14368 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq12645 eq14341
    | exact resolve eq14341 eq12645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14341
  have eq14369 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq12645 eq14360
    | exact resolve eq14360 eq12645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14360
  have eq14377 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq14368
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14368
    | exact resolve eq14368 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq14368
  have eq14378 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq14369
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14369
    | exact resolve eq14369 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14369
  have eq14383 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq12645 eq14377
    | exact resolve eq14377 eq12645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12645 eq14377
  have eq14384 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq12646 eq14378
    | exact resolve eq14378 eq12646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14378
  have eq14385 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq14384
       have r₂ := eq28
       grind)
    | exact resolve eq14384 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14384
  have eq14386 : x = (σ x) := by
    first
    | (have i₁ := eq14385
       have i₂ := eq13856 (σ y)
       grind)
    | exact superpose eq13856 eq14385
    | exact resolve eq14385 eq13856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13856 eq14385
  have eq14387 : x = (σ x) := by
    first
    | (have i₁ := eq14386
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14386
    | exact resolve eq14386 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14386
  have eq14462 : (M.op (σ x) (σ y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq14387 eq12646
    | exact resolve eq12646 eq14387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12646
  have eq14724 : (σ (M.op x y)) = (k x (σ (M.op x y))) := by
    first
    | exact superpose eq14387 eq14383
    | exact resolve eq14383 eq14387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14383 eq14387
  have eq14822 : (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | (have i₁ := eq14724
       have i₂ := eq13888 sF1
       grind)
    | exact superpose eq13888 eq14724
    | exact resolve eq14724 eq13888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13888 eq14724
  have eq14823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14462 eq14822
    | exact resolve eq14822 eq14462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14462 eq14822
  have eq14887 : False := by grind
  exact eq14887

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    grind
  have eq74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq107
    | exact resolve eq107 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq379 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X0 X0) X1 x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq451 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq9913 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq9913
    | exact resolve eq9913 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9913
  have eq9925 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq9914
       have r₂ := eq29
       grind)
    | exact resolve eq9914 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9914
  have eq9931 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq9925
  have eq9961 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq9931
    | exact resolve eq9931 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9931
  have eq10241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq9961 eq108
    | exact resolve eq108 eq9961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq9961
  have eq10250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq10241
  have eq10253 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10250
       have r₂ := eq29
       grind)
    | exact resolve eq10250 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10250
  have eq10381 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10253
  have eq10412 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10381
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq10381
    | exact resolve eq10381 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10381
  have eq10702 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq10412
       grind)
    | exact superpose eq10412 eq46
    | exact resolve eq46 eq10412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq10412
  have eq10718 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq10702
    | exact resolve eq10702 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10702
  have eq10883 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10718 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq10718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq10883
  have eq10888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq10884
    | exact resolve eq10884 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10884
  have eq10899 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq10888
       have r₂ := eq29
       grind)
    | exact resolve eq10888 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10888
  have eq10947 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10899
  have eq10980 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq10947
    | exact resolve eq10947 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10947
  have eq11480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10980 eq10718
    | exact resolve eq10718 eq10980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10718 eq10980
  have eq11483 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11480
  have eq11489 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11483
       have r₂ := eq29
       grind)
    | exact resolve eq11483 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11483
  have eq11492 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq11489 eq31
    | exact resolve eq31 eq11489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq11489
  have eq11612 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq11492
    | exact resolve eq11492 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq11492
  have eq11613 : x = y := by grind
  clear eq11612
  have eq11615 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq11613
       grind)
    | exact superpose eq11613 eq20
    | exact resolve eq20 eq11613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq11616 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11613
       grind)
    | exact superpose eq11613 eq26
    | exact resolve eq26 eq11613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq11613
  have eq11718 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11616
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11616
    | exact resolve eq11616 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq11616
  have eq11719 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11718 eq28
    | exact resolve eq28 eq11718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11718
  have eq11840 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11615
       have i₂ := eq379 X0 x
       grind)
    | (have i₁ := eq11615
       have i₂ := eq379 x X0
       grind)
    | exact superpose eq379 eq11615
    | exact resolve eq11615 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq11615
  have eq11941 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11719 eq11840
    | exact resolve eq11840 eq11719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11719
  have eq11950 : (k (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq64 x
       have i₂ := eq11840 x
       grind)
    | exact superpose eq11840 eq64
    | exact resolve eq64 eq11840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq12057 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq11950
       have i₂ := eq11840 sF0
       grind)
    | exact superpose eq11840 eq11950
    | exact resolve eq11950 eq11840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11950
  have eq12095 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq12057
       have i₂ := eq11840 sF0
       grind)
    | exact superpose eq11840 eq12057
    | exact resolve eq12057 eq11840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12057
  have eq12122 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq11941 eq29
    | exact resolve eq29 eq11941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11941
  have eq12149 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12095 eq451
    | (have j0 := eq451 (M.op x y)
       grind)
    | exact resolve eq451 eq12095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq12095
  have eq12154 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq12149
  have eq12158 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq12154
       have i₂ := eq11840 (σ sF0)
       grind)
    | exact superpose eq11840 eq12154
    | exact resolve eq12154 eq11840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11840 eq12154
  have eq12171 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq22 eq12158
    | exact resolve eq12158 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12158
  have eq12179 : False := by grind
  exact eq12179

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq26 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq26 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq26 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
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
  have eq43 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq43 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq45 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq47 X1 X0
       grind)
    | (have r₁ := eq53 X1 X0
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq53 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq53
  have eq63 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq60
    | (have j0 := eq60 X0 X1
       grind)
    | exact resolve eq60 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq60
  have eq168 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq172 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq168 X0 X1
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq168 X1 X1
       have r₂ := eq63 X1 X1
       grind)
    | exact resolve eq168 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq168
  have eq436 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq172 (σ X0) (σ X1)
       grind)
    | exact superpose eq172 eq15
    | exact resolve eq15 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq436 X0 X1
       have i₂ := eq172 X0 X1
       grind)
    | exact superpose eq172 eq436
    | exact resolve eq436 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq436
  have eq442 : False := by grind
  exact eq442
