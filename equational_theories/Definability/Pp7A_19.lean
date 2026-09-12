import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyx_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = X1 ∨ (M.op X0 X1) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq33 X0 X1 X2 X3
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq33 X0 (M.op X2 X3) X2 X3
       have r₂ := eq12 (M.op X2 X3) (M.op (M.op X0 (M.op X2 X3)) X2)
       grind)
    | (have r₁ := eq33 X1 X0 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq60 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = X1 ∨ (M.op X0 X1) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq32 X0 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq32 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq255 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X3 (M.op X0 X0)
       have i₂ := eq19 X0 X1 X2
       grind)
    | (have i₁ := eq21 X1 X1 (M.op X1 X2)
       have i₂ := eq19 X1 X1 X2
       grind)
    | exact superpose eq19 eq21
    | exact resolve eq21 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21
  have eq900 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq906 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq900 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq900 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq900 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq1610 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq906 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq2375 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq255 X1 X0 x (M.op X1 X0)
       have i₂ := eq59 X1 X0 (M.op X1 X0) (M.op X0 x)
       grind)
    | exact superpose eq59 eq255
    | (have j1 := eq59 X1 X0 x x
       grind)
    | exact resolve eq255 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq255
  have eq2424 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2375 X0 X1
       have j1 := eq1610 X0 X1
       grind)
    | (have r₁ := eq2375 X0 X1
       have r₂ := eq1610 X0 X1
       grind)
    | (have r₁ := eq2375 X1 X0
       have r₂ := eq1610 X0 X1
       grind)
    | exact resolve eq2375 eq1610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610 eq2375
  have eq3672 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2424 (σ X0) (σ X1)
       grind)
    | exact superpose eq2424 eq15
    | exact resolve eq15 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3685 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3672 X0 X1
       have i₂ := eq2424 X0 X1
       grind)
    | exact superpose eq2424 eq3672
    | exact resolve eq3672 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424 eq3672
  have eq3700 : False := by grind
  exact eq3700

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyy_pxx_pyy_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : y ≠ (M.op x y) ∨ (M.op y y) = (k y x) := by
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
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86
    | exact resolve eq86 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq92
    | exact resolve eq92 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : (M.op y y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq108 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq108 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq108 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq111 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq109 (σ X0)
       grind)
    | exact superpose eq109 eq10
    | exact resolve eq10 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq43
    | exact resolve eq43 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq113 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq109 y
       grind)
    | exact superpose eq109 eq74
    | exact resolve eq74 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq114 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq49
    | exact resolve eq49 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq115 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq114
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq114
    | exact resolve eq114 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq109 sF3
       grind)
    | exact superpose eq109 eq113
    | exact resolve eq113 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq112
    | exact resolve eq112 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq118 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq111
    | exact resolve eq111 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq124 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq99
       have i₂ := eq109 sF3
       grind)
    | exact superpose eq109 eq99
    | exact resolve eq99 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq125 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq124
       have i₂ := eq109 y
       grind)
    | exact superpose eq109 eq124
    | exact resolve eq124 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq250 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq109 (τ X0)
       grind)
    | exact superpose eq109 eq34
    | exact resolve eq34 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq307 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq296 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq296
    | exact resolve eq296 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq309 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq307 X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq307
    | exact resolve eq307 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq307
  have eq572 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq657 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50 (M.op X0 X0) X1 X2
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq50 (M.op X2 X2) X1 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op X0 X1) (M.op X1 X2) X3
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq50 (M.op X0 X0) (M.op X0 X0) X2
       have i₂ := eq50 X0 X1 X2
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq50 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y X0
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X0) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X0 X0) X3
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq14 X1 (M.op X1 X2) X2
       have i₂ := eq50 X1 X1 X2
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X0)
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq52 (M.op X2 X2)
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq709 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq657 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq657
    | exact resolve eq657 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq727 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq16
    | exact resolve eq16 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq878 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 (τ X0)
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq52
    | exact resolve eq52 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq53 (τ X0)
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq53
    | exact resolve eq53 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq727
  have eq901 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq118 X1
       grind)
    | exact superpose eq118 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq902 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq901 X0 X1
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq901
    | (have j0 := eq901 X0 X1
       grind)
    | exact resolve eq901 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq1001 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op y y)) = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq902 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq902
    | (have j0 := eq902 y X0
       grind)
    | exact resolve eq902 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq1013 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1001 X0
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq1001
    | (have j0 := eq1001 X0
       grind)
    | exact resolve eq1001 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1001
  have eq1211 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (M.op (σ X0) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq250 (σ X0)
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq250
    | exact resolve eq250 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1248 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (σ X0) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1211 X0
       have i₂ := eq118 (M.op X0 X0)
       grind)
    | exact superpose eq118 eq1211
    | exact resolve eq1211 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1254 : ∀ X0 : G, (M.op (M.op (σ X0) x) (M.op x y)) = (σ (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1248 X0
       have i₂ := eq250 X0
       grind)
    | exact superpose eq250 eq1248
    | exact resolve eq1248 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1515 : ∀ X0 : G, (M.op (M.op x x) (M.op x y)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq669 X0
       have i₂ := eq250 x
       grind)
    | exact superpose eq250 eq669
    | exact resolve eq669 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq1520 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1515 eq14
    | exact resolve eq14 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515
  have eq5737 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (M.op (M.op X0 x) (M.op x y))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq572 X0 X1 X2
       have i₂ := eq250 X0
       grind)
    | exact superpose eq250 eq572
    | exact resolve eq572 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq9608 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (M.op (M.op (σ (k y X0)) (M.op (σ y) X1)) x) (M.op x y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1013 eq692
    | (have j1 := eq1013 X0
       grind)
    | exact resolve eq692 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692 eq1013
  have eq9626 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (σ (k y X0)) (M.op (σ y) X1)) x) (M.op x y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq9608 X0 X1
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq9608
    | (have j0 := eq9608 X0 X1
       grind)
    | exact resolve eq9608 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq9608
  have eq18589 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq667 X0 X1 X2 X3
       have i₂ := eq250 X0
       grind)
    | exact superpose eq250 eq667
    | exact resolve eq667 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq18590 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) x) (M.op x y)) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18589 X0 X1 X2 X3
       have i₂ := eq250 (M.op X0 X1)
       grind)
    | exact superpose eq250 eq18589
    | exact resolve eq18589 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq18589
  have eq18819 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 X2)) x) (M.op x y)) = (M.op (M.op (M.op X1 x) (M.op x y)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18590 X1 (M.op X0 X2) (M.op X2 x) (M.op (M.op X0 X0) x)
       have i₂ := eq686 X0 X2 x x
       grind)
    | exact superpose eq686 eq18590
    | exact resolve eq18590 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq18590
  have eq45397 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x x) (M.op X0 X1)) (M.op (M.op X0 x) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq5737 X0 y X1
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq5737
    | exact resolve eq5737 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq45524 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq5737 eq45397
    | exact resolve eq45397 eq5737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5737 eq45397
  have eq45607 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq45524 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq45524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq45607
    | exact resolve eq45607 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45607
  have eq45625 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq45614
       have r₂ := eq27
       grind)
    | exact resolve eq45614 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45614
  have eq45629 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq45625
    | exact resolve eq45625 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45625
  have eq45673 : (τ (σ y)) = (M.op (M.op (τ (M.op (σ x) (σ x))) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq45629 eq878
    | exact resolve eq878 eq45629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45629
  have eq45815 : (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq878 eq45673
    | exact resolve eq45673 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878 eq45673
  have eq45863 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq45815
    | exact resolve eq45815 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45815
  have eq45875 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq45863
    | exact resolve eq45863 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45863
  have eq45876 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq45875
  have eq45881 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq45876 eq65
    | (have r₁ := eq65
       have r₂ := eq45876
       grind)
    | exact resolve eq65 eq45876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq45876
  have eq45929 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq45881
  have eq47040 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq45929 eq91
    | exact resolve eq91 eq45929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq47047 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq45929 eq45524
    | exact resolve eq45524 eq45929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45524 eq45929
  have eq47054 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq47047
  have eq47064 : (M.op y y) = (k y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq125 eq47040
    | exact resolve eq47040 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47040
  have eq47069 : (M.op y y) = (k y x) ∨ x = y := by
    first
    | (have r₁ := eq47064
       have r₂ := eq64
       grind)
    | exact resolve eq47064 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq47064
  have eq47176 : (τ (σ (M.op x y))) = (M.op y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq47054 eq125
    | exact resolve eq125 eq47054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq47054
  have eq47344 : (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq47176
    | exact resolve eq47176 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq47176
  have eq47457 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) (M.op y X0))) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq709 y y x
       have i₂ := eq47344
       grind)
    | exact superpose eq47344 eq709
    | exact resolve eq709 eq47344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq47344
  have eq47490 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1520 eq47457
    | exact resolve eq47457 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520 eq47457
  have eq47491 : y = (M.op x y) ∨ x = y := by grind
  clear eq47490
  have eq47557 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq47491 eq20
    | exact resolve eq20 eq47491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47491
  have eq47770 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq47557
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47557
    | exact resolve eq47557 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47557
  have eq1444527 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (σ (k y X0)) x) (M.op x y)) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq18819 eq9626
    | (have j0 := eq9626 X0 x
       grind)
    | exact resolve eq9626 eq18819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9626 eq18819
  have eq1444528 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op (M.op (k y X0) x) (M.op x y))) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq1254 eq1444527
    | (have j0 := eq1444527 X0
       grind)
    | exact resolve eq1444527 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254 eq1444527
  have eq1445112 : (σ (M.op x x)) = (M.op (σ (M.op (M.op (M.op y y) x) (M.op x y))) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1444528 x
       have i₂ := eq47069
       grind)
    | exact superpose eq47069 eq1444528
    | (have j0 := eq1444528 x
       grind)
    | exact resolve eq1444528 eq47069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47069 eq1444528
  have eq1445756 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq52 eq1445112
    | exact resolve eq1445112 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1445112
  have eq1446014 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1445756
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1445756
    | exact resolve eq1445756 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445756
  have eq1446015 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1446014
  have eq1446188 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1446015
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq1446015
    | exact resolve eq1446015 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq1446015
  have eq1446269 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1446188
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1446188
    | exact resolve eq1446188 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446188
  have eq1446313 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq1446269
    | exact resolve eq1446269 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446269
  have eq1446543 : (τ (σ y)) = (M.op (M.op (τ (M.op (σ x) (σ x))) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1446313 eq879
    | exact resolve eq879 eq1446313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446313
  have eq1447267 : (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq879 eq1446543
    | exact resolve eq1446543 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879 eq1446543
  have eq1447446 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29 eq1447267
    | exact resolve eq1447267 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1447267
  have eq1447494 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq1447446
    | exact resolve eq1447446 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1447446
  have eq1447495 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1447494
  have eq1447510 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq1447495 eq27
    | exact resolve eq27 eq1447495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447495
  have eq1447838 : x = y := by
    first
    | (have r₁ := eq1447510
       have r₂ := eq47770
       grind)
    | exact resolve eq1447510 eq47770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47770 eq1447510
  have eq1447843 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1447838
       grind)
    | exact superpose eq1447838 eq18
    | exact resolve eq18 eq1447838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1447844 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1447838
       grind)
    | exact superpose eq1447838 eq24
    | exact resolve eq24 eq1447838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1447838
  have eq1448229 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1447844
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1447844
    | exact resolve eq1447844 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1447844
  have eq1448272 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1448229 eq26
    | exact resolve eq26 eq1448229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1448229
  have eq1450372 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1448272 eq115
    | exact resolve eq115 eq1448272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1448272
  have eq1451043 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1450372
       have i₂ := eq1447843
       grind)
    | exact superpose eq1447843 eq1450372
    | exact resolve eq1450372 eq1447843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447843 eq1450372
  have eq1451170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1451043 eq15
    | exact resolve eq15 eq1451043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451043
  have eq1451688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1451170
    | exact resolve eq1451170 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1451170
  have eq1451831 : False := by grind
  exact eq1451831

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxx_pyy_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : y ≠ (M.op x y) ∨ (M.op y y) = (k y x) := by
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
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ X0 ∨ (M.op (M.op X1 X2) (M.op X1 X2)) = (k (M.op X1 X2) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X2) (M.op (M.op X0 X0) X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X1 X2) (M.op (M.op X0 X0) X1)
       grind)
    | (have r₁ := eq13 (M.op X1 X2) (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X1)
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
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
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq111 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq111 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq111 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq112 (σ X0)
       grind)
    | exact superpose eq112 eq10
    | exact resolve eq10 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq43
    | exact resolve eq43 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq116 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq74
    | exact resolve eq74 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq117 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq112 sF2
       grind)
    | exact superpose eq112 eq49
    | exact resolve eq49 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq118 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq117
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq117
    | exact resolve eq117 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq119 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq116
    | exact resolve eq116 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq112 sF2
       grind)
    | exact superpose eq112 eq115
    | exact resolve eq115 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq121 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq114
    | exact resolve eq114 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq128 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq102
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq102
    | exact resolve eq102 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq129 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq128
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq128
    | exact resolve eq128 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq139 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq142 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq112 sF1
       grind)
    | exact superpose eq112 eq139
    | exact resolve eq139 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq145 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq142
       have i₂ := eq112 sF0
       grind)
    | exact superpose eq112 eq142
    | exact resolve eq142 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq142
  have eq167 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq145 eq16
    | exact resolve eq16 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq254 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq485 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq514 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 (σ X0)
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq52
    | exact resolve eq52 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq581 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50 (M.op X0 X0) X1 X2
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq50 (M.op X2 X2) X1 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)))) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) X1 X3
       have i₂ := eq54 X1 X0 X2
       grind)
    | exact superpose eq54 eq50
    | exact resolve eq50 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq50 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y X0
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y) X0
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X0 X3 (M.op X0 X0)
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq54 X1 X1 (M.op X1 X2)
       have i₂ := eq50 X1 X1 X2
       grind)
    | exact superpose eq50 eq54
    | exact resolve eq54 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X0) X3 X4
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq14 (M.op X2 X2) X1 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X0)
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq52 (M.op X2 X2)
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X4)) (M.op X0 X0)) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 (M.op X0 X0) X3 X4
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq54 (M.op X2 X2) X1 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq54
    | exact resolve eq54 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq670 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq670
    | exact resolve eq670 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq825 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq66 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1251 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq254 X0
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq254 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq254
    | exact resolve eq254 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1382 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq259 X0
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq259
    | exact resolve eq259 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq1394 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq1382 eq14
    | exact resolve eq14 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq1584 : ∀ X0 : G, (M.op (M.op x x) (M.op x y)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq682 X0
       have i₂ := eq254 x
       grind)
    | exact superpose eq254 eq682
    | exact resolve eq682 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq1591 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1584 eq14
    | exact resolve eq14 eq1584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1584
  have eq1678 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq683 X0
       have i₂ := eq254 sF2
       grind)
    | exact superpose eq254 eq683
    | exact resolve eq683 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq1689 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1678 eq1394
    | exact resolve eq1394 eq1678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394 eq1678
  have eq3921 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq485 X0 X1 X2
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq485
    | exact resolve eq485 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq3973 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) x) := by
    first
    | exact superpose eq1591 eq3921
    | exact resolve eq3921 eq1591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3975 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1689 eq3921
    | exact resolve eq3921 eq1689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4022 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) x) (M.op x y)) (M.op (M.op (M.op x y) x) (M.op x y))) (M.op (M.op (M.op (M.op x y) x) (M.op x y)) (M.op (M.op (M.op x y) x) (M.op x y)))) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq3973 eq50
    | exact resolve eq50 eq3973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4027 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) x) (M.op x y)) x) (M.op x y)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq4022 X0
       have i₂ := eq254 (M.op (M.op sF0 x) sF0)
       grind)
    | exact superpose eq254 eq4022
    | exact resolve eq4022 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4022
  have eq4030 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq3973 eq4027
    | exact resolve eq4027 eq3973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3973 eq4027
  have eq4411 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq697 X0 X1 x (M.op X0 X1)
       have i₂ := eq50 (M.op X0 X1) (M.op X0 X1) (M.op X1 x)
       grind)
    | (have i₁ := eq697 X0 X0 X0 (M.op X0 X0)
       have i₂ := eq50 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq50 eq697
    | exact resolve eq697 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq697
  have eq4450 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) x) (M.op x y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4411 X0 X1
       have i₂ := eq254 (M.op X0 X1)
       grind)
    | exact superpose eq254 eq4411
    | exact resolve eq4411 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4411
  have eq5091 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq3975 eq703
    | exact resolve eq703 eq3975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5104 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op y X0)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq703 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq703
    | (have j0 := eq703 x y X0
       grind)
    | exact resolve eq703 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5293 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq3921 eq5091
    | exact resolve eq5091 eq3921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3921 eq5091
  have eq5588 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq581 X0 X1 X2
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq581
    | exact resolve eq581 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq5868 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (M.op (M.op X0 x) (M.op x y))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq583 X0 X1 X2
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq583
    | exact resolve eq583 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq6062 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op (M.op X0 X0) (M.op x X1)) x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq5868 eq5588
    | exact resolve eq5588 eq5868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5868
  have eq8203 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X1 X1) X2) (M.op X2 X3)) X4)) x) (M.op x y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5588 (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X1 X1) X2) (M.op X2 X3)) X4)) X1 (M.op X1 X1)
       have i₂ := eq705 (M.op X1 X1) X2 X3 X0 X4
       grind)
    | exact superpose eq705 eq5588
    | exact resolve eq5588 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq5588
  have eq8250 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X4)) x) (M.op x y)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq8203 X0 X1 x x X4
       have i₂ := eq14 X1 x x
       grind)
    | exact superpose eq14 eq8203
    | exact resolve eq8203 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8203
  have eq9242 : ∀ X0 : G, x = (k (M.op (M.op x y) (M.op y X0)) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1591 eq825
    | exact resolve eq825 eq1591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq11760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11761 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11760
    | exact resolve eq11760 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11760
  have eq11772 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11761
       have r₂ := eq27
       grind)
    | exact resolve eq11761 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11761
  have eq11776 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11772
    | exact resolve eq11772 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11772
  have eq11778 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11776
    | exact resolve eq11776 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11776
  have eq11787 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11778 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11778
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11778
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11778
       grind)
    | exact resolve eq12 eq11778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11811 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11778 eq703
    | exact resolve eq703 eq11778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11778
  have eq11828 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5293 eq11811
    | exact resolve eq11811 eq5293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11811
  have eq11838 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11787
       have r₂ := eq26
       grind)
    | exact resolve eq11787 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11787
  have eq11843 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11838
    | exact resolve eq11838 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11838
  have eq11844 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq11843
  have eq11913 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11828 eq728
    | exact resolve eq728 eq11828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11828
  have eq11924 : (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1689 eq11913
    | exact resolve eq11913 eq1689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11913
  have eq11939 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1591 x X0
       have i₂ := eq11924
       grind)
    | exact superpose eq11924 eq1591
    | exact resolve eq1591 eq11924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11970 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq703 y x X0
       have i₂ := eq11924
       grind)
    | exact superpose eq11924 eq703
    | exact resolve eq703 eq11924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11924
  have eq11987 : (M.op y y) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4030 eq11970
    | (have j0 := eq11970 y
       grind)
    | exact resolve eq11970 eq4030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11970
  have eq12001 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52 eq11987
    | exact resolve eq11987 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11987
  have eq12029 : (σ y) = (M.op (M.op (σ (M.op x y)) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq514 y
       have i₂ := eq12001
       grind)
    | exact superpose eq12001 eq514
    | exact resolve eq514 eq12001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12001
  have eq12093 : (σ y) = (M.op (M.op (σ (M.op x y)) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq12029
    | exact resolve eq12029 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12029
  have eq12105 : (σ y) = (M.op (M.op (σ (M.op x y)) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12093
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12093
    | exact resolve eq12093 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12093
  have eq14651 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11844 eq97
    | exact resolve eq97 eq11844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq11844
  have eq14668 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14651
  have eq14682 : (τ (σ (M.op x y))) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14668 eq118
    | exact resolve eq118 eq14668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14668
  have eq14776 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq14682
    | exact resolve eq14682 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14682
  have eq17435 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11939 eq728
    | exact resolve eq728 eq11939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11939
  have eq17607 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq514 x
       have i₂ := eq17435
       grind)
    | exact superpose eq17435 eq514
    | exact resolve eq514 eq17435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17435
  have eq17685 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq17607
    | exact resolve eq17607 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17607
  have eq17697 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17685
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17685
    | exact resolve eq17685 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17685
  have eq19144 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17697 eq12105
    | exact resolve eq12105 eq17697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12105 eq17697
  have eq19194 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq19144
  have eq19200 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19194 eq65
    | (have r₁ := eq65
       have r₂ := eq19194
       grind)
    | exact resolve eq65 eq19194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq19194
  have eq19219 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq19200
  have eq19377 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19219 eq93
    | exact resolve eq93 eq19219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq19219
  have eq19401 : (M.op y y) = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq19377
    | exact resolve eq19377 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19377
  have eq19404 : (M.op y y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19401
       have r₂ := eq64
       grind)
    | exact resolve eq19401 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19401
  have eq19420 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq19404
       grind)
    | exact superpose eq19404 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq19404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19423 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19420
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19420
    | exact resolve eq19420 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19420
  have eq19432 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19423
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19423
    | exact resolve eq19423 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19423
  have eq19434 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19432
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19432
    | exact resolve eq19432 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19432
  have eq22706 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) (M.op y X0))) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq728 y y x
       have i₂ := eq19434
       grind)
    | exact superpose eq19434 eq728
    | exact resolve eq728 eq19434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22724 : (M.op x y) = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1591 eq22706
    | exact resolve eq22706 eq1591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22706
  have eq22787 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) x) (M.op x y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq703 y x X0
       have i₂ := eq22724
       grind)
    | exact superpose eq22724 eq703
    | exact resolve eq703 eq22724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22724
  have eq22807 : (M.op y y) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) (M.op x y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4030 eq22787
    | (have j0 := eq22787 y
       grind)
    | exact resolve eq22787 eq4030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4030 eq22787
  have eq22821 : (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq52 eq22807
    | exact resolve eq22807 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22807
  have eq22909 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) (M.op y X0))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq728 y y x
       have i₂ := eq22821
       grind)
    | exact superpose eq22821 eq728
    | exact resolve eq728 eq22821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22821
  have eq22927 : x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1591 eq22909
    | exact resolve eq22909 eq1591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1591 eq22909
  have eq22928 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq22927
  have eq22955 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22928 eq29
    | exact resolve eq29 eq22928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22928
  have eq23077 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq22955
    | exact resolve eq22955 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22955
  have eq23078 : y = (M.op x y) ∨ x = y := by grind
  clear eq23077
  have eq23492 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq23078 eq20
    | exact resolve eq20 eq23078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23078
  have eq23639 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq23492
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23492
    | exact resolve eq23492 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23492
  have eq23711 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) X0)) (M.op (M.op (σ x) (σ y)) X1)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq23639 eq1689
    | exact resolve eq1689 eq23639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689 eq23639
  have eq27161 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) x) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq675 X0 X1 X2 X3
       have i₂ := eq254 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq254 eq675
    | exact resolve eq675 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq675
  have eq27477 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27161 X0 x x X1
       have i₂ := eq54 x X0 x
       grind)
    | exact superpose eq54 eq27161
    | exact resolve eq27161 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq27161
  have eq74581 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5104 x
       have i₂ := eq14776
       grind)
    | exact superpose eq14776 eq5104
    | exact resolve eq5104 eq14776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5104 eq14776
  have eq74795 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq52 eq74581
    | exact resolve eq74581 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74581
  have eq74796 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq74795
  have eq74856 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq74796
       grind)
    | exact superpose eq74796 eq120
    | exact resolve eq120 eq74796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq74796
  have eq75104 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq74856
    | exact resolve eq74856 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74856
  have eq122137 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq6062 X0 x
       have i₂ := eq27477 (M.op X0 X0) x
       grind)
    | (have i₁ := eq6062 X0 y
       have i₂ := eq27477 (M.op X0 X0) x
       grind)
    | exact superpose eq27477 eq6062
    | (have j0 := eq6062 X0 y
       grind)
    | exact resolve eq6062 eq27477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6062
  have eq122392 : (M.op y x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) (M.op x y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq122137 y
       have i₂ := eq19434
       grind)
    | exact superpose eq19434 eq122137
    | exact resolve eq122137 eq19434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19434 eq122137
  have eq122587 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq52 eq122392
    | exact resolve eq122392 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122392
  have eq122588 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq122587
  have eq122692 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq122588
       grind)
    | exact superpose eq122588 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq122588
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq122588
       grind)
    | exact resolve eq12 eq122588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122588
  have eq122797 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq122692
       have r₂ := eq18
       grind)
    | exact resolve eq122692 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122692
  have eq122819 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq122797
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122797
    | exact resolve eq122797 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122797
  have eq122820 : (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq122819
  have eq124390 : (M.op y y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19404
       have i₂ := eq122820
       grind)
    | exact superpose eq122820 eq19404
    | exact resolve eq19404 eq122820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19404 eq122820
  have eq124418 : (M.op y y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq124390
  have eq125352 : (σ y) = (M.op (M.op (σ (M.op x x)) x) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq514 y
       have i₂ := eq124418
       grind)
    | exact superpose eq124418 eq514
    | exact resolve eq514 eq124418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124418
  have eq125601 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq514 eq125352
    | exact resolve eq125352 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514 eq125352
  have eq125664 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq125601
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq125601
    | exact resolve eq125601 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125601
  have eq125686 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq125664
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq125664
    | exact resolve eq125664 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125664
  have eq125687 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq125686
  have eq125711 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125687 eq26
    | exact resolve eq26 eq125687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125726 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125687 eq129
    | exact resolve eq129 eq125687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq125687
  have eq126072 : (M.op y y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq118 eq125726
    | exact resolve eq125726 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125726
  have eq126111 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125711 eq118
    | exact resolve eq118 eq125711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq126123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125711 eq75104
    | exact resolve eq75104 eq125711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75104 eq125711
  have eq126293 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq126123
  have eq126378 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq126293
       have r₂ := eq27
       grind)
    | exact resolve eq126293 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126293
  have eq127148 : (M.op x x) = (M.op (M.op (M.op (M.op x x) x) (M.op x y)) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4450 y y
       have i₂ := eq126072
       grind)
    | exact superpose eq126072 eq4450
    | exact resolve eq4450 eq126072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4450 eq126072
  have eq127217 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52 eq127148
    | exact resolve eq127148 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq127148
  have eq127326 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq127217
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq127217
    | exact resolve eq127217 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127217
  have eq127541 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq126111
       have i₂ := eq127326
       grind)
    | exact superpose eq127326 eq126111
    | exact resolve eq126111 eq127326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126111 eq127326
  have eq127723 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq127541
  have eq127851 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126378 eq127723
    | exact resolve eq127723 eq126378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126378 eq127723
  have eq127912 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by grind
  clear eq127851
  have eq127922 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq127912
    | exact resolve eq127912 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq127912
  have eq127923 : y = (M.op x y) := by grind
  clear eq127922
  have eq127926 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq127923 eq20
    | exact resolve eq20 eq127923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq127930 : y ≠ y ∨ (M.op y y) = (k y x) := by
    first
    | exact superpose eq127923 eq64
    | (have r₁ := eq64
       have r₂ := eq127923
       grind)
    | exact resolve eq64 eq127923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq128016 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) y) (σ x)) := by
    first
    | exact superpose eq127923 eq3975
    | exact resolve eq3975 eq127923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3975
  have eq128031 : ∀ X0 : G, x = (k (M.op y (M.op y X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq127923 eq9242
    | exact resolve eq9242 eq127923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9242
  have eq128268 : (M.op y y) = (k y x) := by grind
  clear eq127930
  have eq128309 : ∀ X0 : G, x = (k (M.op y (M.op y X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq128031 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq128031
    | (have j0 := eq128031 X0
       grind)
    | exact resolve eq128031 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128031
  have eq128373 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq127926
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq127926
    | exact resolve eq127926 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127926
  have eq128382 : ∀ X0 : G, x = (k (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | exact superpose eq127923 eq128309
    | exact resolve eq128309 eq127923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128309
  have eq128405 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq128373 eq26
    | exact resolve eq26 eq128373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq129455 : (k (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq128268
       grind)
    | exact superpose eq128268 eq73
    | exact resolve eq73 eq128268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq129483 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq129455
       have i₂ := eq119
       grind)
    | exact superpose eq119 eq129455
    | exact resolve eq129455 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq129455
  have eq129494 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq128373 eq129483
    | exact resolve eq129483 eq128373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129483
  have eq129531 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq129494 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq129494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129494
  have eq129532 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq128405 eq129531
    | exact resolve eq129531 eq128405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129531
  have eq129545 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq128405 eq129532
    | exact resolve eq129532 eq128405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129532
  have eq129556 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq128405 eq129545
    | exact resolve eq129545 eq128405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128405 eq129545
  have eq129558 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq129556
       have r₂ := eq27
       grind)
    | exact resolve eq129556 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129556
  have eq129560 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X4)) x) y) := by
    intro X0 X1 X4
    first
    | exact superpose eq127923 eq8250
    | exact resolve eq8250 eq127923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8250
  have eq130005 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op (M.op (M.op X0 X0) x) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129560 (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2)) x
       have i₂ := eq701 X0 X1 X2 (M.op (M.op X0 X1) (M.op X1 X2)) x
       grind)
    | exact superpose eq701 eq129560
    | exact resolve eq129560 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq129560
  have eq130238 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq130005 X0 x x
       have i₂ := eq728 X0 x x
       grind)
    | exact superpose eq728 eq130005
    | exact resolve eq130005 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq130005
  have eq133814 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) x) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq129558 eq703
    | exact resolve eq703 eq129558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703 eq129558
  have eq133899 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5293 eq133814
    | exact resolve eq133814 eq5293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5293 eq133814
  have eq133900 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq133899
  have eq133971 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq133900 eq167
    | exact resolve eq167 eq133900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq134078 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) x) y) := by
    first
    | exact superpose eq133900 eq130238
    | exact resolve eq130238 eq133900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130238 eq133900
  have eq134274 : (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq127923 eq133971
    | exact resolve eq133971 eq127923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133971
  have eq134932 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq134078 eq128016
    | exact resolve eq128016 eq134078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128016
  have eq135139 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq134932 eq23711
    | exact resolve eq23711 eq134932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23711 eq134932
  have eq135278 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq135139 x
       have i₂ := eq1251 sF4 sF4 x
       grind)
    | exact superpose eq1251 eq135139
    | exact resolve eq135139 eq1251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251 eq135139
  have eq135315 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) x) y) ∨ x = y := by
    first
    | exact superpose eq127923 eq135278
    | exact resolve eq135278 eq127923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135278
  have eq135335 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq134078 eq135315
    | exact resolve eq135315 eq134078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134078 eq135315
  have eq135358 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq135335 eq28
    | exact resolve eq28 eq135335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq135335
  have eq135834 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq135358
    | exact resolve eq135358 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq135358
  have eq135908 : x = y ∨ x = y := by
    first
    | exact superpose eq127923 eq135834
    | exact resolve eq135834 eq127923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135834
  have eq135909 : x = y := by grind
  clear eq135908
  have eq136091 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq135909
       grind)
    | exact superpose eq135909 eq24
    | exact resolve eq24 eq135909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq136187 : ∀ X0 : G, x = (k (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq128382 X0
       have i₂ := eq135909
       grind)
    | exact superpose eq135909 eq128382
    | exact resolve eq128382 eq135909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128382 eq135909
  have eq136197 : x = (k (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq136187 x
       have i₂ := eq27477 x x
       grind)
    | (have i₁ := eq136187 y
       have i₂ := eq27477 x x
       grind)
    | exact superpose eq27477 eq136187
    | (have j0 := eq136187 y
       grind)
    | exact resolve eq136187 eq27477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27477 eq136187
  have eq136279 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq128373 eq136091
    | exact resolve eq136091 eq128373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128373 eq136091
  have eq136281 : x = (k (M.op x y) x) := by
    first
    | exact superpose eq127923 eq136197
    | exact resolve eq136197 eq127923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136197
  have eq136363 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq136279
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq136279
    | exact resolve eq136279 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136279
  have eq136365 : x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq136281
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq136281
    | exact resolve eq136281 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq136281
  have eq136434 : x = (k y x) := by
    first
    | exact superpose eq127923 eq136365
    | exact resolve eq136365 eq127923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127923 eq136365
  have eq136472 : x = (M.op y y) := by
    first
    | (have i₁ := eq136434
       have i₂ := eq128268
       grind)
    | exact superpose eq128268 eq136434
    | exact resolve eq136434 eq128268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128268 eq136434
  have eq136496 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq136472
       have i₂ := eq134274
       grind)
    | exact superpose eq134274 eq136472
    | exact resolve eq136472 eq134274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134274 eq136472
  have eq137111 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq136496 eq15
    | exact resolve eq15 eq136496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136496
  have eq137209 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq137111
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq137111
    | exact resolve eq137111 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq137111
  have eq137248 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq136363 eq137209
    | exact resolve eq137209 eq136363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136363 eq137209
  have eq137275 : False := by grind
  exact eq137275

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pyy_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq51
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq62 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq62
  have eq158 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq162 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq158 X0 X1
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq158 X0 X1
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq158 X0 X0
       have r₂ := eq65 X0 X0
       grind)
    | exact resolve eq158 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq158
  have eq422 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq162 (σ X0) (σ X1)
       grind)
    | exact superpose eq162 eq15
    | exact resolve eq15 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq422 X0 X1
       have i₂ := eq162 X0 X1
       grind)
    | exact superpose eq162 eq422
    | exact resolve eq422 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq422
  have eq429 : False := by grind
  exact eq429

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyx_pxx_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq25 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq27 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq25 (τ X0)
       grind)
    | exact superpose eq25 eq19
    | (have j1 := eq25 (τ X0)
       grind)
    | exact resolve eq19 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq25
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq110
    | (have j0 := eq110 X0
       grind)
    | exact resolve eq110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq118 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq114
    | (have j0 := eq114 X0
       grind)
    | exact resolve eq114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq122 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq118 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq118 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq118 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq127 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq27
    | (have j0 := eq27 X0 X1
       have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq27 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq122 (σ X0)
       grind)
    | exact superpose eq122 eq15
    | exact resolve eq15 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq148 X0
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq148
    | exact resolve eq148 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq148
  have eq2133 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq127 x y
       grind)
    | exact superpose eq127 eq16
    | (have j1 := eq127 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq127 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq127 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq127 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq2165 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq2133
  have eq2202 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2165
       grind)
    | exact superpose eq2165 eq16
    | exact resolve eq16 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2204 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2165
       grind)
    | exact superpose eq2165 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2165
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2165
       grind)
    | exact resolve eq12 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165
  have eq2225 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq2204
  have eq2235 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2225
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2225
    | exact resolve eq2225 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225
  have eq4367 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2235
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq2235
    | (have j1 := eq14 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq2235 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2235
  have eq4396 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq4367
  have eq4409 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4396
       have r₂ := eq2202
       grind)
    | exact resolve eq4396 eq2202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202 eq4396
  have eq6879 : y ≠ y ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq4409
       grind)
    | exact superpose eq4409 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq4409
       grind)
    | exact resolve eq12 eq4409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6914 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6879
  have eq11823 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq27 x y
       have i₂ := eq6914
       grind)
    | exact superpose eq6914 eq27
    | (have j0 := eq27 x y
       grind)
    | exact resolve eq27 eq6914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6914
  have eq11826 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11823
  have eq18463 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq11826
       grind)
    | exact superpose eq11826 eq16
    | exact resolve eq16 eq11826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11826
  have eq36762 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18463
       have i₂ := eq4409
       grind)
    | exact superpose eq4409 eq18463
    | exact resolve eq18463 eq4409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4409 eq18463
  have eq36763 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq36762
  have eq36764 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq36763
  have eq47863 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq36764
       grind)
    | exact superpose eq36764 eq10
    | exact resolve eq10 eq36764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36764
  have eq47920 : x = y ∨ x = y := by
    first
    | (have i₁ := eq47863
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq47863
    | exact resolve eq47863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47863
  have eq47921 : x = y := by grind
  clear eq47920
  have eq66007 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47921
       grind)
    | exact superpose eq47921 eq16
    | exact resolve eq16 eq47921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47921
  have eq66008 : False := by grind
  exact eq66008

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X1 X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op (M.op X1 X1) X0) X2
       have i₂ := eq9 X1 (M.op X1 X1) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq120 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq120 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq120 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq120 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq123 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq122 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq122
    | exact resolve eq122 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq122 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq122
    | exact resolve eq122 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq125 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq124
    | exact resolve eq124 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq126 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq123 X0
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq123
    | exact resolve eq123 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq123
  have eq161 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) X2) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X2 X1
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq9
    | exact resolve eq9 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq168 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X3) (M.op X3 X2)) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X3 X2
       have i₂ := eq168 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq168 X0 X0
       grind)
    | exact superpose eq168 eq9
    | (have j1 := eq168 X0 X1
       grind)
    | exact resolve eq9 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X1 X2) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq57 X1 X2 X0
       grind)
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq685 : ∀ X0 X3 : G, (M.op X3 X3) = (M.op X3 X0) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq632 x X3 X0 (M.op x x)
       have i₂ := eq245 X0 X3 x x
       grind)
    | exact superpose eq245 eq632
    | (have j1 := eq245 X0 X3 x X3
       grind)
    | exact resolve eq632 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq831 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq168 X0 X1
       have i₂ := eq685 X0 X1
       grind)
    | (have i₁ := eq168 x x
       have i₂ := eq685 X0 x
       grind)
    | exact superpose eq685 eq168
    | (have j0 := eq168 X0 X1
       have j1 := eq685 X0 X1
       grind)
    | exact resolve eq168 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq832 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X2 X3)) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq245 X0 X1 X3 X2
       have i₂ := eq685 X0 X1
       grind)
    | (have i₁ := eq245 X3 X3 X2 X3
       have i₂ := eq685 X0 X3
       grind)
    | exact superpose eq685 eq245
    | (have j0 := eq245 X0 X1 X2 X3
       have j1 := eq685 X0 X1
       grind)
    | exact resolve eq245 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq685
  have eq856 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X2 X3)) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq832 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq857 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq831 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq861 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq856 X0 X1 x x
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq856
    | (have j0 := eq856 X0 X1 x x
       grind)
    | exact resolve eq856 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq960 : ∀ X0 X1 X2 X3 : G, (τ X1) = (M.op (M.op (τ (M.op X0 X0)) X2) (M.op X2 X3)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq161 X1 X3 X2
       have i₂ := eq857 X0 X1
       grind)
    | (have i₁ := eq161 X0 X1 X2
       have i₂ := eq857 X0 X1
       grind)
    | exact superpose eq857 eq161
    | (have j1 := eq857 X0 X1
       grind)
    | exact resolve eq161 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq1000 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq960 X0 X1 x x
       have i₂ := eq161 X0 x x
       grind)
    | exact superpose eq161 eq960
    | (have j0 := eq960 X0 X1 x x
       grind)
    | exact resolve eq960 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq960
  have eq1016 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1000 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1000
    | (have j0 := eq1000 (σ X0) (σ X1)
       grind)
    | exact resolve eq1000 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1040 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1016 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1016
    | (have j0 := eq1016 X0 X1
       grind)
    | exact resolve eq1016 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq1045 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1040 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1040
    | (have j0 := eq1040 X0 X1
       grind)
    | exact resolve eq1040 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1149 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1045 x y
       grind)
    | exact superpose eq1045 eq16
    | (have j1 := eq1045 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1045 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1045 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1169 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1149
       have i₂ := eq861 x y
       grind)
    | exact superpose eq861 eq1149
    | (have j1 := eq861 x y
       grind)
    | (have r₁ := eq1149
       have r₂ := eq861 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1149
       have r₂ := eq861 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1149 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq1149
  have eq1176 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by grind
  clear eq1169
  have eq1177 : x = y := by grind
  clear eq1176
  have eq1181 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1177
       grind)
    | exact superpose eq1177 eq16
    | exact resolve eq16 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1182 : False := by grind
  exact eq1182

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pxx_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq44 (k X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq44 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq35 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq46 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq47 X1 X0
       grind)
    | (have r₁ := eq52 X1 X0
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq52 X0 (M.op X1 X1)
       have r₂ := eq47 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq52 X1 X1
       have r₂ := eq47 (k X1 X1) X1
       grind)
    | exact resolve eq52 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq52
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq56
    | (have j0 := eq56 X0 X1
       grind)
    | exact resolve eq56 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq57
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq66 X0 X1
       have r₂ := eq65 X0 X1
       grind)
    | exact resolve eq66 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq66
  have eq166 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq170 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq166 X0 X1
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq166 X1 X1
       have r₂ := eq68 X1 X1
       grind)
    | (have r₁ := eq166 X1 X0
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq166 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq166
  have eq307 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq170 (σ X1) (σ X0)
       grind)
    | exact superpose eq170 eq15
    | exact resolve eq15 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X1
       have i₂ := eq170 X1 X0
       grind)
    | exact superpose eq170 eq307
    | exact resolve eq307 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq307
  have eq313 : False := by grind
  exact eq313

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pyy_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq44
    | (have j1 := eq76 y x
       grind)
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq105
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
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
    | (have r₁ := eq118 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq118 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq119 x
       grind)
    | exact superpose eq119 eq43
    | exact resolve eq43 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq123 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq119 y
       grind)
    | exact superpose eq119 eq74
    | exact resolve eq74 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
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
  clear eq124
  have eq128 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq119 sF3
       grind)
    | exact superpose eq119 eq123
    | exact resolve eq123 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq129 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq122
       have i₂ := eq119 sF2
       grind)
    | exact superpose eq119 eq122
    | exact resolve eq122 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq122
  have eq254 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq595 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50 (M.op X0 X0) X1 X2
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq50 (M.op X2 X2) X1 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq801 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y) X0
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X0 (M.op X0 X0) X3
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq51 X1 (M.op X1 X2) X2
       have i₂ := eq50 X1 X1 X2
       grind)
    | exact superpose eq50 eq51
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X0) X3 X4
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq14 (M.op X2 X2) X1 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq788 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq788
    | exact resolve eq788 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq849 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq109 eq76
    | (have j0 := eq76 (σ y) (σ x)
       grind)
    | exact resolve eq76 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq850 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq849
    | exact resolve eq849 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq853 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq850
       have r₂ := eq27
       grind)
    | exact resolve eq850 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq855 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq853
    | exact resolve eq853 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq860 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq855 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq855
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq855
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq855
       grind)
    | exact resolve eq12 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq855 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq863 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq861
    | exact resolve eq861 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq864 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq860
       have r₂ := eq26
       grind)
    | exact resolve eq860 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq979 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq864 eq109
    | exact resolve eq109 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq982 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq979
  have eq1176 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ y) x) (M.op x y)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq982 eq254
    | exact resolve eq254 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq1382 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq259 X0
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq259
    | exact resolve eq259 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq1439 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) x) (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq855 eq1382
    | exact resolve eq1382 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq1382
  have eq1529 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1176 eq1439
    | exact resolve eq1439 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176 eq1439
  have eq1540 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1529
  have eq1551 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (M.op X0 X0) X1)) X0) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1540 eq54
    | exact resolve eq54 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540
  have eq1581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1551 x x
       have i₂ := eq54 x sF1 x
       grind)
    | exact superpose eq54 eq1551
    | exact resolve eq1551 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1551
  have eq1586 : (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1581
       have r₂ := eq27
       grind)
    | exact resolve eq1581 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq1595 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq50 X0 y x
       have i₂ := eq1586
       grind)
    | exact superpose eq1586 eq50
    | exact resolve eq50 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1596 : ∀ X0 : G, (M.op (M.op y y) (M.op y y)) = (M.op (M.op x y) (M.op x X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq50 y x X0
       have i₂ := eq1586
       grind)
    | exact superpose eq1586 eq50
    | exact resolve eq50 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1599 : ∀ X0 : G, (M.op (M.op y x) (M.op x y)) = (M.op (M.op x y) (M.op x X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1596 X0
       have i₂ := eq254 y
       grind)
    | exact superpose eq254 eq1596
    | exact resolve eq1596 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1600 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1595 X0
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq1595
    | exact resolve eq1595 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595
  have eq1693 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1599 X0
       have i₂ := eq1586
       grind)
    | exact superpose eq1586 eq1599
    | exact resolve eq1599 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586
  have eq1716 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1693 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq1723 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op y x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1716 eq1599
    | (have j0 := eq1599 y
       grind)
    | exact resolve eq1599 eq1716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599 eq1716
  have eq1732 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op y x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1723
  have eq1735 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq801 X0
       have i₂ := eq254 sF2
       grind)
    | exact superpose eq254 eq801
    | exact resolve eq801 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq1755 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1600 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1600
    | (have j0 := eq1600 x
       grind)
    | exact resolve eq1600 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600
  have eq1817 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1755 eq14
    | exact resolve eq14 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq1875 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1817 eq254
    | exact resolve eq254 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq1898 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq52 eq1875
    | exact resolve eq1875 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875
  have eq1903 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq1898
       grind)
    | exact superpose eq1898 eq129
    | exact resolve eq129 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1898
  have eq1937 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1903
    | exact resolve eq1903 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq1943 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1937 eq51
    | exact resolve eq51 eq1937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1937
  have eq3997 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq595 X0 X1 X2
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq595
    | exact resolve eq595 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq4149 : y = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1732 eq3997
    | exact resolve eq3997 eq1732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732
  have eq4224 : y = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4149
       have i₂ := eq254 sF0
       grind)
    | exact superpose eq254 eq4149
    | exact resolve eq4149 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq4149
  have eq4236 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4224 eq3997
    | exact resolve eq3997 eq4224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4224
  have eq4266 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq128
       have i₂ := eq4236
       grind)
    | exact superpose eq4236 eq128
    | exact resolve eq128 eq4236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq4236
  have eq4310 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4266
    | exact resolve eq4266 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4266
  have eq4317 : (σ y) = (M.op (M.op (σ (M.op x y)) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4310 eq52
    | exact resolve eq52 eq4310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq4310
  have eq4413 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4317 eq1943
    | exact resolve eq1943 eq4317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943 eq4317
  have eq4432 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4413
  have eq4437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4432
    | exact resolve eq4432 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4432
  have eq4438 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4437
       have r₂ := eq27
       grind)
    | exact resolve eq4437 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4437
  have eq4953 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq4438 eq27
    | exact resolve eq27 eq4438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq4957 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq4438 eq863
    | (have r₁ := eq863
       have r₂ := eq4438
       grind)
    | exact resolve eq863 eq4438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq4961 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq4957
  have eq6347 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq4961 eq109
    | exact resolve eq109 eq4961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq4961
  have eq6350 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq6347
  have eq6356 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq6350
       have r₂ := eq4953
       grind)
    | exact resolve eq6350 eq4953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6350
  have eq6384 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq3997 y x x
       have i₂ := eq6356
       grind)
    | exact superpose eq6356 eq3997
    | exact resolve eq3997 eq6356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6356
  have eq6470 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y X1)) := by
    intro X1
    first
    | exact superpose eq6384 eq816
    | exact resolve eq816 eq6384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq7675 : ∀ X0 X1 X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op y X0)) X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq819 x y X0 X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq819
    | (have j0 := eq819 x y X0 X1 X2
       grind)
    | exact resolve eq819 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq819
  have eq8221 : ∀ X1 X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) X1) (M.op X1 X2)) := by
    intro X1 X2
    first
    | exact superpose eq6470 eq7675
    | exact resolve eq7675 eq6470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6470 eq7675
  have eq8249 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq8221 x x
       have i₂ := eq14 sF0 x x
       grind)
    | exact superpose eq14 eq8221
    | exact resolve eq8221 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8221
  have eq8316 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq3997 x x x
       have i₂ := eq8249
       grind)
    | exact superpose eq8249 eq3997
    | exact resolve eq3997 eq8249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8322 : x = y := by
    first
    | exact superpose eq6384 eq8316
    | exact resolve eq8316 eq6384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6384 eq8316
  have eq8344 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8322
       grind)
    | exact superpose eq8322 eq24
    | exact resolve eq24 eq8322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8322
  have eq8400 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq8344
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8344
    | exact resolve eq8344 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8344
  have eq8979 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq8400 eq4953
    | exact resolve eq4953 eq8400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4953
  have eq9133 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ y) X0) X1)) (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ y) X0) X1))) := by
    intro X0 X1
    first
    | exact superpose eq1735 eq846
    | exact resolve eq846 eq1735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846 eq1735
  have eq9410 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ x) X0) X1)) (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ x) X0) X1))) := by
    intro X0 X1
    first
    | exact superpose eq8400 eq9133
    | exact resolve eq9133 eq8400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9133
  have eq9446 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3997 eq9410
    | exact resolve eq9410 eq3997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3997 eq9410
  have eq9460 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4438 eq9446
    | exact resolve eq9446 eq4438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4438 eq9446
  have eq9465 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8400 eq9460
    | exact resolve eq9460 eq8400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8400 eq9460
  have eq9468 : (τ (σ x)) = (M.op x x) := by
    first
    | exact superpose eq9465 eq127
    | exact resolve eq127 eq9465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq9465
  have eq9539 : (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9468
       have i₂ := eq8249
       grind)
    | exact superpose eq8249 eq9468
    | exact resolve eq9468 eq8249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8249 eq9468
  have eq9542 : x = (M.op x y) := by
    first
    | exact superpose eq28 eq9539
    | exact resolve eq9539 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9539
  have eq9545 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq9542 eq20
    | exact resolve eq20 eq9542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9542
  have eq9646 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq9545
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9545
    | exact resolve eq9545 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9545
  have eq9665 : False := by grind
  exact eq9665
