import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_y_pxy_pxx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq43
    | (have j0 := eq43 (σ X0) (σ X1)
       grind)
    | exact resolve eq43 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq19
    | exact resolve eq19 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq88 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq88
    | exact resolve eq88 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq88
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq194 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq56 x y
       grind)
    | exact superpose eq56 eq16
    | (have j1 := eq56 x y
       grind)
    | exact resolve eq16 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq229 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq9
    | exact resolve eq9 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq194
       have i₂ := eq100 x
       grind)
    | exact superpose eq100 eq194
    | exact resolve eq194 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq901 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq900
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq900
    | (have j1 := eq43 x y
       grind)
    | exact resolve eq900 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq900
  have eq902 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq901
  have eq974 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq902
       grind)
    | exact superpose eq902 eq10
    | exact resolve eq10 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq1009 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq974
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq974
    | exact resolve eq974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq1010 : y = (M.op x x) := by grind
  clear eq1009
  have eq1021 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq229 x X0
       have i₂ := eq1010
       grind)
    | exact superpose eq1010 eq229
    | exact resolve eq229 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq1037 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq25 x x
       have i₂ := eq1010
       grind)
    | exact superpose eq1010 eq25
    | exact resolve eq25 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1010
  have eq2218 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1021 (M.op (σ y) (σ y))
       have i₂ := eq9 (σ y) (σ y) (σ y)
       grind)
    | exact superpose eq9 eq1021
    | exact resolve eq1021 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq2230 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2218
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq2218
    | exact resolve eq2218 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq2218
  have eq2233 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2230
       have i₂ := eq1037
       grind)
    | exact superpose eq1037 eq2230
    | exact resolve eq2230 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037 eq2230
  have eq2235 : False := by grind
  exact eq2235

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_pyx_pxx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
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
  clear eq44
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq81
    | exact resolve eq81 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq86
    | exact resolve eq86 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq90 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq103 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq110 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq110 x
       have r₂ := eq13 x x
       grind)
    | exact resolve eq110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq111 (σ X0)
       grind)
    | exact superpose eq111 eq10
    | exact resolve eq10 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq73
    | exact resolve eq73 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq116 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq49
    | exact resolve eq49 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq117 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq116
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq116
    | exact resolve eq116 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq115
    | exact resolve eq115 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq113
    | exact resolve eq113 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq125 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq103
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq103
    | exact resolve eq103 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq126 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq125
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq125
    | exact resolve eq125 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq251 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq251 eq50
    | exact resolve eq50 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq111 (τ X0)
       grind)
    | exact superpose eq111 eq34
    | exact resolve eq34 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq371 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq360 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq360
    | exact resolve eq360 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq374 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq371
    | exact resolve eq371 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq371
  have eq553 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq14
    | exact resolve eq14 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X1 X2
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq14
    | exact resolve eq14 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq583 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq665 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq664 X0 X1 X2 X3
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq664
    | exact resolve eq664 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq666 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq663
    | exact resolve eq663 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq663
  have eq820 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq374 X0
       grind)
    | exact superpose eq374 eq16
    | exact resolve eq16 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq1085 : ∀ X0 : G, (τ X0) = (M.op y (M.op (M.op x y) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq820 X0
       grind)
    | exact superpose eq820 eq50
    | exact resolve eq50 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq1309 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq253 eq50
    | exact resolve eq50 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq1324 : (M.op (M.op x y) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq251 eq1309
    | exact resolve eq1309 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309
  have eq1804 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq620 X0 X0 X0
       grind)
    | exact superpose eq620 eq14
    | exact resolve eq14 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1805 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq620 X0 X0 X0
       grind)
    | exact superpose eq620 eq50
    | exact resolve eq50 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1806 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq620 X0 X0 X0
       grind)
    | exact superpose eq620 eq51
    | exact resolve eq51 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1818 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f1818_12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
      intro X0 X1
      grind
    have f1818_13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X2 X2))) = X2 := by
      intro X0 X1 X2
      grind
    have f1818_22 : X0 ≠ (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) := by grind
    have f1818_88 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f1818_12 (M.op x (M.op x x)) X1
         have i₂ := f1818_13 x x x
         grind)
      | exact superpose f1818_13 f1818_12
      | exact resolve f1818_12 f1818_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1818_113 : X0 ≠ X0 := by
      first
      | (have i₁ := f1818_22
         have i₂ := f1818_88 X0 X1
         grind)
      | exact superpose f1818_88 f1818_22
      | (have r₁ := f1818_22
         have r₂ := f1818_88 X0 X1
         grind)
      | exact resolve f1818_22 f1818_88
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1818_116 : False := by grind
    exact f1818_116
  clear eq620 eq656
  have eq1881 : (M.op x y) = (M.op y (M.op y (M.op y (M.op x y)))) := by
    first
    | exact superpose eq1324 eq259
    | exact resolve eq259 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq1324
  have eq2086 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq583 X0
       have i₂ := eq1805 X0
       grind)
    | exact superpose eq1805 eq583
    | exact resolve eq583 eq1805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2113 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1805 eq588
    | exact resolve eq588 eq1805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805
  have eq2123 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq588 eq2113
    | exact resolve eq2113 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113
  have eq2159 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq2086
    | exact resolve eq2086 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2086
  have eq2374 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1806 eq588
    | exact resolve eq588 eq1806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1806
  have eq2384 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq588 eq2374
    | exact resolve eq2374 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq2374
  have eq2724 : y = (M.op (M.op x y) (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq1818 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1818
    | (have j0 := eq1818 y x
       grind)
    | exact resolve eq1818 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5877 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq665 X0 X1 X2 X3
       have i₂ := eq666 X0 X1
       grind)
    | exact superpose eq666 eq665
    | exact resolve eq665 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq666
  have eq6139 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5877 X0 (M.op X0 (M.op X0 X0)) X2 x
       have i₂ := eq583 X0
       grind)
    | exact superpose eq583 eq5877
    | exact resolve eq5877 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq5877
  have eq17561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17561
    | exact resolve eq17561 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17561
  have eq17567 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17562
       have r₂ := eq27
       grind)
    | exact resolve eq17562 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17562
  have eq17569 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17567
    | exact resolve eq17567 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17567
  have eq17571 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17569
    | exact resolve eq17569 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17569
  have eq17574 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17571 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq17571
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq17571
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17571
       grind)
    | exact resolve eq12 eq17571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17571
  have eq17613 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17574
       have r₂ := eq26
       grind)
    | exact resolve eq17574 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17574
  have eq17616 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17613
    | exact resolve eq17613 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17613
  have eq17617 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq17616
  have eq17799 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17617 eq91
    | exact resolve eq91 eq17617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq17617
  have eq17804 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17799
  have eq17811 : (τ (σ (M.op x y))) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17804 eq117
    | exact resolve eq117 eq17804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq17841 : (τ (σ x)) = (M.op y (M.op (M.op x y) (τ (σ (M.op x y))))) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17804 eq1085
    | exact resolve eq1085 eq17804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085 eq17804
  have eq17896 : (τ (σ x)) = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq17841
    | exact resolve eq17841 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17841
  have eq17900 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq17811
    | exact resolve eq17811 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17811
  have eq17901 : (τ (σ x)) = (M.op y (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq251 eq17896
    | exact resolve eq17896 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq17896
  have eq17904 : x = (M.op y (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq17901
    | exact resolve eq17901 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17901
  have eq18797 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17904 eq1881
    | exact resolve eq1881 eq17904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1881 eq17904
  have eq18833 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18797
  have eq18871 : x = (M.op (M.op x y) (M.op x (M.op x x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1818 x y
       have i₂ := eq18833
       grind)
    | exact superpose eq18833 eq1818
    | exact resolve eq1818 eq18833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818
  have eq19596 : (M.op y x) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18871 eq589
    | exact resolve eq589 eq18871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq18871
  have eq19668 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17900
       have i₂ := eq19596
       grind)
    | exact superpose eq19596 eq17900
    | exact resolve eq17900 eq19596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17900 eq19596
  have eq19701 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19668
  have eq20931 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (M.op X0 X0))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq553 x X0
       have i₂ := eq19701
       grind)
    | exact superpose eq19701 eq553
    | exact resolve eq553 eq19701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq19701
  have eq21027 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (M.op X0 X0))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq20931
    | (have j0 := eq20931 X0
       grind)
    | exact resolve eq20931 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20931
  have eq21073 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (M.op X0 X0))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq21027 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21027
    | (have j0 := eq21027 X0
       grind)
    | exact resolve eq21027 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21027
  have eq21344 : ∀ X0 : G, (σ X0) = (M.op x (M.op (M.op x y) (σ (M.op X0 X0)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq556 X0 x y
       have i₂ := eq18833
       grind)
    | exact superpose eq18833 eq556
    | exact resolve eq556 eq18833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq28241 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1804 X0 x y
       have i₂ := eq18833
       grind)
    | exact superpose eq18833 eq1804
    | exact resolve eq1804 eq18833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804
  have eq29889 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6139 X0 x y
       have i₂ := eq18833
       grind)
    | exact superpose eq18833 eq6139
    | exact resolve eq6139 eq18833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6139 eq18833
  have eq45898 : (σ (M.op x y)) = (M.op (σ x) (M.op x (M.op (M.op x y) (σ (M.op x y))))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21073 sF1
       have i₂ := eq28241 sF1
       grind)
    | exact superpose eq28241 eq21073
    | exact resolve eq21073 eq28241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21073 eq28241
  have eq45960 : (σ (M.op x y)) = (M.op (σ x) (M.op x (M.op (M.op x y) (σ (M.op x y))))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45898
  have eq51644 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2724 eq29889
    | exact resolve eq29889 eq2724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724 eq29889
  have eq51842 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51644
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq51644
    | exact resolve eq51644 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51644
  have eq52168 : (σ y) = (M.op x (M.op (M.op x y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21344 y
       have i₂ := eq51842
       grind)
    | exact superpose eq51842 eq21344
    | exact resolve eq21344 eq51842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21344 eq51842
  have eq52216 : (σ y) = (M.op x (M.op (M.op x y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq52168
  have eq52240 : (σ y) = (M.op x (M.op (M.op x y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq52216
    | exact resolve eq52216 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52216
  have eq52296 : (σ y) = (M.op x (M.op (M.op x y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52240
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq52240
    | exact resolve eq52240 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq52240
  have eq54341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq52296 eq45960
    | exact resolve eq45960 eq52296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45960 eq52296
  have eq54389 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq54341
  have eq54401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq54389
    | exact resolve eq54389 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54389
  have eq54402 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq54401
       have r₂ := eq27
       grind)
    | exact resolve eq54401 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54401
  have eq54448 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54402 eq2384
    | exact resolve eq2384 eq54402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384
  have eq54463 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq54448
    | exact resolve eq54448 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54448
  have eq54473 : (τ (M.op (σ x) (σ y))) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54463 eq126
    | exact resolve eq126 eq54463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq54463
  have eq54772 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2159 y
       have i₂ := eq54473
       grind)
    | exact superpose eq54473 eq2159
    | exact resolve eq2159 eq54473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54473
  have eq55272 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54402 eq54772
    | exact resolve eq54772 eq54402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54402 eq54772
  have eq55319 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) := by grind
  clear eq55272
  have eq55330 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq55319
    | exact resolve eq55319 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq55319
  have eq55336 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq55330
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55330
    | exact resolve eq55330 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55330
  have eq55337 : x = (M.op x y) := by grind
  clear eq55336
  have eq55339 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq55337 eq20
    | exact resolve eq20 eq55337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq55437 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq55337 eq2123
    | exact resolve eq2123 eq55337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123
  have eq55469 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq55437
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55437
    | exact resolve eq55437 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq55437
  have eq55528 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq55339
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq55339
    | exact resolve eq55339 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55339
  have eq55529 : x = (M.op y y) := by
    first
    | exact superpose eq55337 eq55469
    | exact resolve eq55469 eq55337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55337 eq55469
  have eq55566 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq55528 eq26
    | exact resolve eq26 eq55528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq55773 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq55529
       grind)
    | exact superpose eq55529 eq118
    | exact resolve eq118 eq55529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq55529
  have eq55999 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq55773
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq55773
    | exact resolve eq55773 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq55773
  have eq56032 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq55528 eq55999
    | exact resolve eq55999 eq55528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55528 eq55999
  have eq56210 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq56032 eq2159
    | exact resolve eq2159 eq56032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2159 eq56032
  have eq56289 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55566 eq56210
    | exact resolve eq56210 eq55566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55566 eq56210
  have eq56333 : False := by grind
  exact eq56333

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pxy_pyx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq30 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq81 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq81 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq81 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq86 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq82 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq82
    | exact resolve eq82 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq82 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq82
    | exact resolve eq82 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq88 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq87
    | exact resolve eq87 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq89 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq86
    | exact resolve eq86 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq86
  have eq130 : ∀ X0 X1 X2 : G, (τ X0) = (M.op X2 (M.op (M.op X1 X2) (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X2 X1
       have i₂ := eq88 X0
       grind)
    | exact superpose eq88 eq9
    | exact resolve eq9 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq137 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq140 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq56 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq56
    | exact resolve eq56 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X2 X3) (M.op X0 X1))) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X3 X2
       have i₂ := eq137 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq137 X1 X1
       grind)
    | exact superpose eq137 eq9
    | (have j1 := eq137 X0 X1
       grind)
    | exact resolve eq9 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq140 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq65 X1 X1
       grind)
    | exact superpose eq65 eq140
    | exact resolve eq140 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq140
  have eq415 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X1 X0 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq179
    | (have j0 := eq179 X0 X1 x x
       grind)
    | exact resolve eq179 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq179
  have eq1684 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X0 (M.op X0 X0) X2 X1
       have i₂ := eq225 X0 X0
       grind)
    | exact superpose eq225 eq61
    | exact resolve eq61 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1855 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X1
       have i₂ := eq1684 X1 X2 X0
       grind)
    | exact superpose eq1684 eq58
    | exact resolve eq58 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1856 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq225 X1 X3
       have i₂ := eq1684 X1 X2 X0
       grind)
    | exact superpose eq1684 eq225
    | exact resolve eq225 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq1880 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 (M.op X0 X1) X1 X3 X2
       have i₂ := eq1684 X1 X1 X0
       grind)
    | exact superpose eq1684 eq61
    | exact resolve eq61 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1905 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1880 X0 X1 x x
       have i₂ := eq61 X1 X1 x x
       grind)
    | exact superpose eq61 eq1880
    | exact resolve eq1880 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1880
  have eq2541 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) = (M.op (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1855 X0 (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) (M.op X1 X2)
       have i₂ := eq1856 X3 X2 (M.op X0 (M.op X1 X2)) X1
       grind)
    | exact superpose eq1856 eq1855
    | exact resolve eq1855 eq1856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855 eq1856
  have eq2571 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2541 X0 X1 X2 X3
       have i₂ := eq1905 (M.op X3 (M.op X0 (M.op X1 X2))) X2
       grind)
    | exact superpose eq1905 eq2541
    | exact resolve eq2541 eq1905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905 eq2541
  have eq3517 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2571 X1 X0 X1 X1
       have i₂ := eq415 X0 X1
       grind)
    | exact superpose eq415 eq2571
    | (have j1 := eq415 X0 X1
       grind)
    | exact resolve eq2571 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571
  have eq5978 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 X1
       have i₂ := eq3517 X0 X1
       grind)
    | (have i₁ := eq137 X1 X1
       have i₂ := eq3517 X0 X1
       grind)
    | exact superpose eq3517 eq137
    | (have j0 := eq137 X0 X1
       have j1 := eq3517 X0 X1
       grind)
    | exact resolve eq137 eq3517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq5989 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X1 X1))) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq415 X0 X1
       have i₂ := eq3517 X0 X1
       grind)
    | (have i₁ := eq415 X1 X1
       have i₂ := eq3517 X0 X1
       grind)
    | exact superpose eq3517 eq415
    | (have j0 := eq415 X0 X1
       have j1 := eq3517 X0 X1
       grind)
    | exact resolve eq415 eq3517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq3517
  have eq6109 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X1 X1))) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5989 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5989
  have eq6116 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5978 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5978
  have eq6132 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6109 X0 X1
       have i₂ := eq58 X1
       grind)
    | exact superpose eq58 eq6109
    | (have j0 := eq6109 X0 X1
       grind)
    | exact resolve eq6109 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq6109
  have eq6420 : ∀ X0 X1 X2 X3 : G, (τ X1) = (M.op X2 (M.op (M.op X3 X2) (τ (M.op X0 X0)))) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq130 X1 X3 X2
       have i₂ := eq6116 X0 X1
       grind)
    | (have i₁ := eq130 X0 X1 X2
       have i₂ := eq6116 X0 X1
       grind)
    | exact superpose eq6116 eq130
    | (have j1 := eq6116 X0 X1
       grind)
    | exact resolve eq130 eq6116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6116
  have eq6509 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6420 X0 X1 x x
       have i₂ := eq130 X0 x x
       grind)
    | exact superpose eq130 eq6420
    | (have j0 := eq6420 X0 X1 x x
       grind)
    | exact resolve eq6420 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq6420
  have eq6533 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6509 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6509
    | (have j0 := eq6509 (σ X0) (σ X1)
       grind)
    | exact resolve eq6509 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6509
  have eq6562 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6533 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq6533
    | (have j0 := eq6533 X0 X1
       grind)
    | exact resolve eq6533 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6533
  have eq6568 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6562 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6562
    | (have j0 := eq6562 X0 X1
       grind)
    | exact resolve eq6562 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6562
  have eq6878 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq6568 y x
       grind)
    | exact superpose eq6568 eq16
    | (have j1 := eq6568 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq6568 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq6568 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq6568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6568
  have eq7217 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq6878
       have i₂ := eq6132 y x
       grind)
    | exact superpose eq6132 eq6878
    | (have j1 := eq6132 x y
       grind)
    | (have r₁ := eq6878
       have r₂ := eq6132 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6878
       have r₂ := eq6132 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6878 eq6132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6132 eq6878
  have eq7222 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by grind
  clear eq7217
  have eq7223 : x = y := by grind
  clear eq7222
  have eq7231 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7223
       grind)
    | exact superpose eq7223 eq16
    | exact resolve eq16 eq7223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7223
  have eq7232 : False := by grind
  exact eq7232

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxy_x_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq13 X0 (M.op X0 X0)
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
  have eq175 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq175 (M.op sF0 sF0)
       have i₂ := eq16 sF0 sF0 sF0
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq176 (M.op sF4 sF4)
       have i₂ := eq16 sF4 sF4 sF4
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq188 eq176
    | exact resolve eq176 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq188 eq16
    | exact resolve eq16 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : (M.op x y) = (k x y) ∨ y = (M.op x x) := by
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
  have eq594 : ∀ X0 : G, (M.op y (k (M.op x y) (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq28 sF0 (M.op X0 X0)
       grind)
    | exact superpose eq28 eq175
    | (have j1 := eq28 X0 (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq175 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq607 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq590
       grind)
    | exact superpose eq590 eq41
    | exact resolve eq41 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq613
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq613
    | exact resolve eq613 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq616 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq614
    | exact resolve eq614 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq626 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq616 eq596
    | exact resolve eq596 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq626
       have r₂ := eq27
       grind)
    | exact resolve eq626 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq638 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq633 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq633 eq13
    | exact resolve eq13 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 X0))) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq633 eq16
    | exact resolve eq16 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq633 eq176
    | exact resolve eq176 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq638
       have r₂ := eq640
       grind)
    | exact resolve eq638 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq640
  have eq646 : (τ (σ y)) = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq645 eq98
    | exact resolve eq98 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq645
  have eq652 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq646
    | exact resolve eq646 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq646
  have eq658 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 : G, (M.op (k X0 X1) (k X0 X1)) = (M.op X1 (k X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq178
    | (have j1 := eq28 (k X0 X1) (M.op X1 (k X0 X1))
       grind)
    | exact resolve eq178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq633 eq178
    | exact resolve eq178 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq178 X0 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op X1 X0)
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq176
    | exact resolve eq176 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op X1 X0)
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq175
    | exact resolve eq175 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq669
    | exact resolve eq669 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq691 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq687
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq687
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq687 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq687 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq687 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq687 eq176
    | exact resolve eq176 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq188 eq698
    | exact resolve eq698 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq702 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq693
       have r₂ := eq695
       grind)
    | exact resolve eq693 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq695
  have eq713 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq702 eq607
    | (have j0 := eq607 (σ y)
       grind)
    | exact resolve eq607 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq825 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq633 eq641
    | exact resolve eq641 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq687 eq641
    | exact resolve eq641 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq836 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by grind
  clear eq826
  have eq837 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq825
  have eq842 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq687 eq837
    | exact resolve eq837 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq844 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq842 eq178
    | exact resolve eq178 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq842 eq195
    | exact resolve eq195 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq847 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq842 eq13
    | exact resolve eq13 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq842 eq16
    | exact resolve eq16 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq849 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq836 eq846
    | exact resolve eq846 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq846
  have eq851 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq633 eq844
    | exact resolve eq844 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq855 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq849 eq642
    | exact resolve eq642 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq859 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq849 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq855
  have eq882 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq861 eq701
    | exact resolve eq701 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq890 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq882
  have eq1012 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq178 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq177 X0 x x X3
       grind)
    | exact superpose eq177 eq178
    | exact resolve eq178 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1016 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq177 X1 x x X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1020 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq177 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq177 eq176
    | exact resolve eq176 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1023 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1020 X0 X1
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq1020
    | exact resolve eq1020 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq2745 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq633 eq658
    | exact resolve eq658 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2767 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x x) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq848 sF2
       have i₂ := eq658 sF2
       grind)
    | exact superpose eq658 eq848
    | (have j1 := eq658 (σ x)
       grind)
    | exact resolve eq848 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq2773 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq633 eq2767
    | exact resolve eq2767 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767
  have eq2778 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq2745
    | exact resolve eq2745 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2745
  have eq2783 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq633 eq2773
    | exact resolve eq2773 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq2773
  have eq2789 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq616 eq2783
    | exact resolve eq2783 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783
  have eq2794 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2778 eq616
    | exact resolve eq616 eq2778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2798 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2778 eq153
    | exact resolve eq153 eq2778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq2778
  have eq2800 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2794
  have eq2802 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq2798
    | exact resolve eq2798 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2798
  have eq2805 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq590 eq2802
    | exact resolve eq2802 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2802
  have eq2812 : x = (M.op y (M.op (M.op x y) y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq2800
       grind)
    | exact superpose eq2800 eq175
    | exact resolve eq175 eq2800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2822 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq2800
       grind)
    | exact superpose eq2800 eq178
    | exact resolve eq178 eq2800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2825 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2822
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2822
    | exact resolve eq2822 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822
  have eq2841 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq2805
       grind)
    | exact superpose eq2805 eq178
    | exact resolve eq178 eq2805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2805
  have eq2844 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2841
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2841
    | exact resolve eq2841 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2841
  have eq2858 : y ≠ (M.op x y) ∨ (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2825
       grind)
    | exact superpose eq2825 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2825
       grind)
    | exact resolve eq13 eq2825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2860 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq2825
       grind)
    | exact superpose eq2825 eq28
    | exact resolve eq28 eq2825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2874 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2858
       have r₂ := eq2860
       grind)
    | exact resolve eq2858 eq2860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858 eq2860
  have eq2982 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op X1 X0) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X0 X1
       have i₂ := eq2844
       grind)
    | exact superpose eq2844 eq16
    | exact resolve eq16 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2992 : y ≠ (M.op x y) ∨ (M.op x y) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2844
       grind)
    | exact superpose eq2844 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2844
       grind)
    | exact resolve eq13 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2994 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq2844
       grind)
    | exact superpose eq2844 eq28
    | exact resolve eq28 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2844
  have eq3009 : (M.op x y) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2992
       have r₂ := eq2994
       grind)
    | exact resolve eq2992 eq2994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992 eq2994
  have eq3024 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq2874
       grind)
    | exact superpose eq2874 eq41
    | exact resolve eq41 eq2874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874
  have eq3029 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3024
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3024
    | exact resolve eq3024 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3024
  have eq3031 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3029
    | exact resolve eq3029 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3029
  have eq3047 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq3009
       grind)
    | exact superpose eq3009 eq41
    | exact resolve eq41 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3009
  have eq3052 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3047
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3047
    | exact resolve eq3047 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3047
  have eq3054 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3052
    | exact resolve eq3052 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3052
  have eq3187 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2789 eq849
    | exact resolve eq849 eq2789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq3189 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2789 eq642
    | exact resolve eq642 eq2789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq3193 : (σ x) ≠ (σ y) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2789 eq13
    | exact resolve eq13 eq2789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3195 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2789 eq28
    | (have j0 := eq28 (M.op (σ x) (σ y)) (σ y)
       grind)
    | exact resolve eq28 eq2789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2789
  have eq3222 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3189
  have eq3224 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3187
  have eq3230 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq188 eq3195
    | exact resolve eq3195 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3195
  have eq3231 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2800 eq3193
    | exact resolve eq3193 eq2800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3193
  have eq3233 : (σ x) = (σ y) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq861 eq3230
    | exact resolve eq3230 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3230
  have eq3235 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2800 eq3233
    | exact resolve eq3233 eq2800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3233
  have eq3237 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq3235
       have r₂ := eq3231
       grind)
    | exact resolve eq3235 eq3231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3231 eq3235
  have eq3248 : y = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq658 x
       have i₂ := eq3224
       grind)
    | exact superpose eq3224 eq658
    | exact resolve eq658 eq3224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3253 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq3224
       grind)
    | exact superpose eq3224 eq178
    | exact resolve eq178 eq3224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3257 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3253
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3253
    | exact resolve eq3253 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3253
  have eq3259 : x = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3248
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3248
    | exact resolve eq3248 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3248
  have eq3273 : y ≠ (M.op x y) ∨ (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq3257
       grind)
    | exact superpose eq3257 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq3257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3275 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq3257
       grind)
    | exact superpose eq3257 eq28
    | exact resolve eq28 eq3257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3290 : (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq3273
       have r₂ := eq3275
       grind)
    | exact resolve eq3273 eq3275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3273 eq3275
  have eq3305 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq3290
       grind)
    | exact superpose eq3290 eq41
    | exact resolve eq41 eq3290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3290
  have eq3310 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3305
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3305
    | exact resolve eq3305 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3305
  have eq3312 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq3310
    | exact resolve eq3310 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3310
  have eq3723 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3222 eq890
    | exact resolve eq890 eq3222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq3222
  have eq3753 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3723
  have eq3763 : x = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq3753
       grind)
    | exact superpose eq3753 eq175
    | exact resolve eq175 eq3753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq3770 : y = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq658 x
       have i₂ := eq3753
       grind)
    | exact superpose eq3753 eq658
    | exact resolve eq658 eq3753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq3775 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq3753
       grind)
    | exact superpose eq3753 eq178
    | exact resolve eq178 eq3753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3781 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3775
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3775
    | exact resolve eq3775 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775
  have eq3783 : x = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3770
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3770
    | exact resolve eq3770 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770
  have eq3873 : (τ (σ x)) = (k y y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3237 eq116
    | exact resolve eq116 eq3237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3237
  have eq3900 : y = (M.op x x) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq30 eq3873
    | exact resolve eq3873 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3873
  have eq4064 : x ≠ y ∨ y = (k x x) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq3900
       grind)
    | exact superpose eq3900 eq13
    | exact resolve eq13 eq3900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4066 : y = (k x x) ∨ x = y ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq3900
       grind)
    | exact superpose eq3900 eq28
    | exact resolve eq28 eq3900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4068 : (M.op x y) = (M.op y y) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq3900
       grind)
    | exact superpose eq3900 eq178
    | exact resolve eq178 eq3900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4074 : (M.op x y) = (M.op y y) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4068
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4068
    | exact resolve eq4068 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4068
  have eq4075 : y = (k x x) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq4064
       have r₂ := eq4066
       grind)
    | exact resolve eq4064 eq4066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4064 eq4066
  have eq4492 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq674 x
       have i₂ := eq3753
       grind)
    | exact superpose eq3753 eq674
    | exact resolve eq674 eq3753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4495 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq674 x
       have i₂ := eq2800
       grind)
    | exact superpose eq2800 eq674
    | exact resolve eq674 eq2800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4533 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4495
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4495
    | exact resolve eq4495 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4495
  have eq4536 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4492
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4492
    | exact resolve eq4492 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4492
  have eq4548 : (M.op x x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4533 eq178
    | exact resolve eq178 eq4533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4533
  have eq4563 : y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2800 eq4548
    | exact resolve eq4548 eq2800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2800 eq4548
  have eq4657 : (M.op x x) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4536 eq178
    | exact resolve eq178 eq4536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4536
  have eq4672 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3753 eq4657
    | exact resolve eq4657 eq3753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4657
  have eq4877 : y ≠ (M.op x y) ∨ (M.op x y) = (k y y) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq4074
       grind)
    | exact superpose eq4074 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq4074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4879 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq4074
       grind)
    | exact superpose eq4074 eq28
    | exact resolve eq28 eq4074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4074
  have eq4897 : (M.op x y) = (k y y) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq4877
       have r₂ := eq4879
       grind)
    | exact resolve eq4877 eq4879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4877 eq4879
  have eq4902 : (σ y) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4075
       grind)
    | exact superpose eq4075 eq40
    | exact resolve eq40 eq4075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4075
  have eq4907 : (σ y) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4902
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4902
    | exact resolve eq4902 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4902
  have eq4909 : (σ y) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4907
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4907
    | exact resolve eq4907 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4907
  have eq5221 : x ≠ (M.op x y) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4897
  have eq6379 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    first
    | exact superpose eq184 eq176
    | exact resolve eq176 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7157 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq3259
       grind)
    | exact superpose eq3259 eq41
    | exact resolve eq41 eq3259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3259
  have eq7159 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq7157
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7157
    | exact resolve eq7157 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7157
  have eq8516 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq3783
       grind)
    | exact superpose eq3783 eq41
    | exact resolve eq41 eq3783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3783
  have eq8518 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq8516
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8516
    | exact resolve eq8516 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8516
  have eq8524 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7159 eq596
    | exact resolve eq596 eq7159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7159
  have eq8530 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq8524
  have eq8601 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8530 eq178
    | exact resolve eq178 eq8530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8530
  have eq8627 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq8601
    | exact resolve eq8601 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8601
  have eq8697 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8627 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq8627
       grind)
    | exact resolve eq13 eq8627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8699 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8627 eq28
    | exact resolve eq28 eq8627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8627
  have eq8721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3031 eq8699
    | exact resolve eq8699 eq3031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3031 eq8699
  have eq8722 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3312 eq8697
    | exact resolve eq8697 eq3312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3312 eq8697
  have eq8731 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq8721
       have r₂ := eq27
       grind)
    | exact resolve eq8721 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8721
  have eq8732 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq8722
       have r₂ := eq27
       grind)
    | exact resolve eq8722 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8722
  have eq8736 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq8732
       have r₂ := eq8731
       grind)
    | exact resolve eq8732 eq8731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8731 eq8732
  have eq8739 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8736 eq180
    | exact resolve eq180 eq8736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq8833 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq8739
       have r₂ := eq8518
       grind)
    | exact resolve eq8739 eq8518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8518 eq8739
  have eq8850 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8833 eq616
    | exact resolve eq616 eq8833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8854 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq8850
  have eq8864 : x = (M.op (σ y) (M.op (M.op (σ x) (σ y)) y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq176 x
       have i₂ := eq8854
       grind)
    | exact superpose eq8854 eq176
    | exact resolve eq176 eq8854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8879 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq674 x
       have i₂ := eq8854
       grind)
    | exact superpose eq8854 eq674
    | exact resolve eq674 eq8854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8885 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq8854
       grind)
    | exact superpose eq8854 eq178
    | exact resolve eq178 eq8854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8892 : y = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq681 x x
       have i₂ := eq8854
       grind)
    | exact superpose eq8854 eq681
    | exact resolve eq681 eq8854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8893 : y = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8892
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8892
    | exact resolve eq8892 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8892
  have eq8896 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8885
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8885
    | exact resolve eq8885 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8885
  have eq8898 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8879
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8879
    | exact resolve eq8879 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8879
  have eq8901 : x = (M.op (σ y) (M.op (σ x) y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8736 eq8864
    | exact resolve eq8864 eq8736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8864
  have eq8902 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6379 eq8893
    | exact resolve eq8893 eq6379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8893
  have eq8940 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq8896
       grind)
    | exact superpose eq8896 eq28
    | exact resolve eq28 eq8896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8896
  have eq8962 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq8940
  have eq9000 : (M.op x x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8898 eq178
    | exact resolve eq178 eq8898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8898
  have eq9025 : y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8854 eq9000
    | exact resolve eq9000 eq8854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9000
  have eq9275 : (M.op (M.op x y) y) = (M.op y (M.op (M.op x y) x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3763 eq682
    | exact resolve eq682 eq3763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9278 : (M.op (M.op x y) y) = (M.op y (M.op (M.op x y) x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2812 eq682
    | exact resolve eq682 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq9316 : (M.op y y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4563 eq9278
    | exact resolve eq9278 eq4563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4563 eq9278
  have eq9319 : (M.op y y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4672 eq9275
    | exact resolve eq9275 eq4672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4672 eq9275
  have eq9455 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2825 eq9316
    | exact resolve eq9316 eq2825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2825 eq9316
  have eq9458 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3781 eq9319
    | exact resolve eq9319 eq3781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3781 eq9319
  have eq9663 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq184 eq1016
    | exact resolve eq1016 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9667 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 X1)) (M.op X1 y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq1016 X1 X0 x
       have i₂ := eq3224
       grind)
    | exact superpose eq3224 eq1016
    | exact resolve eq1016 eq3224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3224
  have eq9677 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq1016 X1 X0 y
       have i₂ := eq3257
       grind)
    | exact superpose eq3257 eq1016
    | exact resolve eq1016 eq3257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3257
  have eq9725 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq176 (M.op X0 (M.op X0 X0))
       have i₂ := eq1016 X0 X0 X0
       grind)
    | exact superpose eq1016 eq176
    | exact resolve eq176 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9799 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq8736 eq9677
    | exact resolve eq9677 eq8736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9677
  have eq9803 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq8736 eq9667
    | exact resolve eq9667 eq8736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9667
  have eq9834 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9663 eq9799
    | exact resolve eq9799 eq9663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9799
  have eq9838 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9663 eq9803
    | exact resolve eq9803 eq9663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9803
  have eq9848 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9834 eq9838
    | exact resolve eq9838 eq9834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9838
  have eq9967 : x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9455 eq2812
    | exact resolve eq2812 eq9455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2812 eq9455
  have eq10013 : x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9967
  have eq10020 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq182 eq10013
    | exact resolve eq10013 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10013
  have eq10112 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10020 eq28
    | exact resolve eq28 eq10020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10020
  have eq10150 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq9848 eq10112
    | exact resolve eq10112 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10112
  have eq10363 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9458 eq3763
    | exact resolve eq3763 eq9458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3763 eq9458
  have eq10398 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq10363
  have eq10405 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq182 eq10398
    | exact resolve eq10398 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq10398
  have eq10457 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq10405 eq13
    | exact resolve eq13 eq10405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10405
  have eq10494 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq10457
       have r₂ := eq10150
       grind)
    | exact resolve eq10457 eq10150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10150 eq10457
  have eq10978 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9834 eq184
    | exact resolve eq184 eq9834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9834
  have eq11066 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq10978 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq10978
       grind)
    | exact resolve eq13 eq10978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10978
  have eq11089 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq11066
  have eq11128 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11089 eq42
    | exact resolve eq42 eq11089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11089
  have eq11138 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq11128
    | exact resolve eq11128 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11128
  have eq12066 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8902 eq681
    | exact resolve eq681 eq8902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8902
  have eq12109 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (M.op (σ x) y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8736 eq12066
    | exact resolve eq12066 eq8736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8736 eq12066
  have eq12115 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8901 eq12109
    | exact resolve eq12109 eq8901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8901 eq12109
  have eq12221 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12115 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq12115
       grind)
    | exact resolve eq13 eq12115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12223 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12115 eq28
    | exact resolve eq28 eq12115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12115
  have eq12265 : x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12221
       have r₂ := eq12223
       grind)
    | exact resolve eq12221 eq12223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12221 eq12223
  have eq13735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3054 eq691
    | exact resolve eq691 eq3054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq3054
  have eq13769 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13735
       have r₂ := eq713
       grind)
    | exact resolve eq13735 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq13735
  have eq13771 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13769
       have r₂ := eq27
       grind)
    | exact resolve eq13769 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13769
  have eq13801 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13771 eq674
    | exact resolve eq674 eq13771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13771
  have eq13854 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq687 eq13801
    | exact resolve eq13801 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq13801
  have eq13870 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq861 eq13854
    | exact resolve eq13854 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq13854
  have eq13897 : x = (M.op (σ y) (M.op (M.op (σ x) (σ y)) y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq176 x
       have i₂ := eq13870
       grind)
    | exact superpose eq13870 eq176
    | exact resolve eq176 eq13870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13927 : y = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq681 x x
       have i₂ := eq13870
       grind)
    | exact superpose eq13870 eq681
    | exact resolve eq681 eq13870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13870
  have eq13932 : y = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13927
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13927
    | exact resolve eq13927 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13927
  have eq13949 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6379 eq13932
    | exact resolve eq13932 eq6379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6379 eq13932
  have eq14382 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13949 eq681
    | exact resolve eq681 eq13949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14422 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13897 eq14382
    | exact resolve eq14382 eq13897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13897 eq14382
  have eq14537 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14422 eq28
    | exact resolve eq28 eq14422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14422
  have eq14560 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq14537
  have eq18861 : y = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2982 (M.op sF0 sF0) (M.op x x)
       have i₂ := eq659 sF0 x x
       grind)
    | exact superpose eq659 eq2982
    | exact resolve eq2982 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659 eq2982
  have eq18990 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18861
       have i₂ := eq178 sF0 sF0
       grind)
    | exact superpose eq178 eq18861
    | exact resolve eq18861 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18861
  have eq19091 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13949 eq18990
    | exact resolve eq18990 eq13949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13949 eq18990
  have eq19347 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19091 eq184
    | exact resolve eq184 eq19091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq19091
  have eq19496 : y ≠ (M.op x y) ∨ (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq19347
       grind)
    | exact superpose eq19347 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19498 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq19347
       grind)
    | exact superpose eq19347 eq28
    | exact resolve eq28 eq19347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19347
  have eq19537 : (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19496
       have r₂ := eq19498
       grind)
    | exact resolve eq19496 eq19498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19496 eq19498
  have eq19562 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq19537
       grind)
    | exact superpose eq19537 eq41
    | exact resolve eq41 eq19537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19573 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19562
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19562
    | exact resolve eq19562 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19562
  have eq19577 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq19573
    | exact resolve eq19573 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19573
  have eq19581 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9848 eq19577
    | exact resolve eq19577 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9848 eq19577
  have eq19596 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19581 eq116
    | exact resolve eq116 eq19581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19581
  have eq19646 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq19596
    | exact resolve eq19596 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19596
  have eq19650 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19537 eq19646
    | exact resolve eq19646 eq19537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19537 eq19646
  have eq19651 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19650
  have eq19657 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19651 eq27
    | exact resolve eq27 eq19651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19658 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19651 eq176
    | exact resolve eq176 eq19651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq19660 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19651 eq188
    | exact resolve eq188 eq19651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq19683 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19651 eq847
    | (have r₁ := eq847
       have r₂ := eq19651
       grind)
    | exact resolve eq847 eq19651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq19753 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq19683
  have eq19967 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19658 (M.op X0 (M.op X0 X0))
       have i₂ := eq1016 X0 X0 X0
       grind)
    | exact superpose eq1016 eq19658
    | exact resolve eq19658 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19658
  have eq20867 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19753 eq142
    | exact resolve eq142 eq19753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq19753
  have eq20883 : y = (M.op x x) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq20867
    | exact resolve eq20867 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20867
  have eq21092 : x = (M.op x (M.op x y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq674 x
       have i₂ := eq20883
       grind)
    | exact superpose eq20883 eq674
    | exact resolve eq674 eq20883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20883
  have eq21135 : x = (k x x) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21092
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21092
    | exact resolve eq21092 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21092
  have eq21309 : x = y ∨ y = (M.op x x) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq652
       have i₂ := eq21135
       grind)
    | exact superpose eq21135 eq652
    | exact resolve eq652 eq21135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21329 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq607 x
       have i₂ := eq21135
       grind)
    | exact superpose eq21135 eq607
    | (have j0 := eq607 x
       grind)
    | (have r₁ := eq607 x
       have r₂ := eq21135
       grind)
    | exact resolve eq607 eq21135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607 eq21135
  have eq21331 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq21329
  have eq21352 : x = y ∨ x = y ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21331 eq21309
    | exact resolve eq21309 eq21331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21309 eq21331
  have eq21353 : x = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq21352
  have eq21380 : (M.op x x) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21353 eq178
    | exact resolve eq178 eq21353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21353
  have eq22727 : y = (M.op (M.op x y) x) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3900
       have i₂ := eq21380
       grind)
    | exact superpose eq21380 eq3900
    | exact resolve eq3900 eq21380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3900 eq21380
  have eq22841 : y = (M.op (M.op x y) x) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq22727
       have r₂ := eq5221
       grind)
    | exact resolve eq22727 eq5221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22727
  have eq22870 : y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq9025 eq22841
    | exact resolve eq22841 eq9025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22841
  have eq22879 : y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9025 eq22870
    | exact resolve eq22870 eq9025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9025 eq22870
  have eq22884 : y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22879
       have r₂ := eq19657
       grind)
    | exact resolve eq22879 eq19657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22879
  have eq23337 : (M.op x y) = (M.op y y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22884 eq178
    | exact resolve eq178 eq22884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22884
  have eq23377 : (M.op x y) = (M.op y y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23337
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23337
    | exact resolve eq23337 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23337
  have eq23527 : y ≠ (M.op x y) ∨ (M.op x y) = (k y y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq23377
       grind)
    | exact superpose eq23377 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq23377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23529 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq23377
       grind)
    | exact superpose eq23377 eq28
    | exact resolve eq28 eq23377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23377
  have eq23568 : (M.op x y) = (k y y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23527
       have r₂ := eq23529
       grind)
    | exact resolve eq23527 eq23529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23527 eq23529
  have eq23628 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq23568
       grind)
    | exact superpose eq23568 eq41
    | exact resolve eq41 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23568
  have eq23643 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23628
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23628
    | exact resolve eq23628 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23628
  have eq23649 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq23643
    | exact resolve eq23643 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23643
  have eq23653 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14560 eq23649
    | exact resolve eq23649 eq14560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14560 eq23649
  have eq23753 : (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23653 eq4909
    | exact resolve eq4909 eq23653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4909 eq23653
  have eq23802 : (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq23753
       have r₂ := eq5221
       grind)
    | exact resolve eq23753 eq5221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5221 eq23753
  have eq23830 : (σ (M.op x y)) = (σ x) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq10494 eq23802
    | exact resolve eq23802 eq10494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10494 eq23802
  have eq23831 : (σ (M.op x y)) = (σ x) ∨ x = (k y y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq23830
  have eq23848 : (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq12265 eq23831
    | exact resolve eq23831 eq12265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12265 eq23831
  have eq23849 : x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq23848
  have eq23920 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq23849 eq42
    | exact resolve eq42 eq23849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq23849
  have eq23933 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq23920
    | exact resolve eq23920 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23920
  have eq23938 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23933
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23933
    | exact resolve eq23933 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23933
  have eq23965 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq23938 eq11138
    | exact resolve eq11138 eq23938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11138 eq23938
  have eq23974 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq23965
  have eq24018 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq23974 eq859
    | exact resolve eq859 eq23974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859 eq23974
  have eq24105 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq24018
       have r₂ := eq3753
       grind)
    | exact resolve eq24018 eq3753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3753 eq24018
  have eq24124 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8833 eq24105
    | exact resolve eq24105 eq8833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8833 eq24105
  have eq24767 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq24124 eq616
    | exact resolve eq616 eq24124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq24124
  have eq24771 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq24767
  have eq28397 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq24771
  have eq28416 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq28397
       have r₂ := eq8854
       grind)
    | exact resolve eq28397 eq8854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8854 eq28397
  have eq28511 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq28416
       grind)
    | exact superpose eq28416 eq178
    | exact resolve eq178 eq28416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28416
  have eq28540 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28511
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28511
    | exact resolve eq28511 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28511
  have eq28629 : y ≠ (M.op x y) ∨ (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq28540
       grind)
    | exact superpose eq28540 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq28540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28540
  have eq28669 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq28629
       have r₂ := eq8962
       grind)
    | exact resolve eq28629 eq8962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8962 eq28629
  have eq28784 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq28669
       grind)
    | exact superpose eq28669 eq41
    | exact resolve eq41 eq28669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28669
  have eq28797 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28784
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28784
    | exact resolve eq28784 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28784
  have eq28801 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq28797
    | exact resolve eq28797 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28797
  have eq36141 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq674 X0
       have i₂ := eq19967 X0
       grind)
    | exact superpose eq19967 eq674
    | exact resolve eq674 eq19967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq19967
  have eq36451 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq36141
    | (have j0 := eq36141 (σ y)
       grind)
    | exact resolve eq36141 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36141
  have eq36575 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19651 eq36451
    | exact resolve eq36451 eq19651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19651 eq36451
  have eq36593 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19660 eq36575
    | exact resolve eq36575 eq19660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19660 eq36575
  have eq36621 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq36593 eq177
    | exact resolve eq177 eq36593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq36593
  have eq36670 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36621 x x
       have i₂ := eq1012 sF3 (M.op x x)
       grind)
    | exact superpose eq1012 eq36621
    | exact resolve eq36621 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012 eq36621
  have eq36737 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36670 eq13
    | exact resolve eq13 eq36670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36739 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36670 eq28
    | exact resolve eq28 eq36670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36670
  have eq36785 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq36737
       have r₂ := eq36739
       grind)
    | exact resolve eq36737 eq36739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36737 eq36739
  have eq36969 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36785 eq28801
    | exact resolve eq28801 eq36785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28801 eq36785
  have eq36979 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq36969
  have eq37015 : x = (M.op x y) := by
    first
    | (have r₁ := eq36979
       have r₂ := eq19657
       grind)
    | exact resolve eq36979 eq19657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19657 eq36979
  have eq37047 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq37015
       grind)
    | exact superpose eq37015 eq18
    | exact resolve eq18 eq37015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq37048 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq37015
       grind)
    | exact superpose eq37015 eq22
    | exact resolve eq22 eq37015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq37050 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq37015
       grind)
    | exact superpose eq37015 eq40
    | exact resolve eq40 eq37015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq37051 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq590
       have i₂ := eq37015
       grind)
    | exact superpose eq37015 eq590
    | exact resolve eq590 eq37015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq37052 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq652
       have i₂ := eq37015
       grind)
    | exact superpose eq37015 eq652
    | exact resolve eq652 eq37015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq37249 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq37048 eq20
    | exact resolve eq20 eq37048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37408 : y ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq37047 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq37047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39086 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq37051 eq41
    | exact resolve eq41 eq37051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq37051
  have eq39089 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq39086
    | exact resolve eq39086 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39086
  have eq39092 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq37249 eq39089
    | exact resolve eq39089 eq37249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39089
  have eq39650 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq39092 eq596
    | exact resolve eq596 eq39092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq39092
  have eq42459 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq39650 eq178
    | exact resolve eq178 eq39650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq39650
  have eq42499 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq42459
    | exact resolve eq42459 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42459
  have eq42581 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq42499 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq42499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42583 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq42499 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq42499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42499
  have eq42619 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq42581
       have r₂ := eq42583
       grind)
    | exact resolve eq42581 eq42583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42581 eq42583
  have eq46836 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq851 eq1023
    | exact resolve eq1023 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq1023
  have eq46956 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq46836
    | exact resolve eq46836 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46836
  have eq47044 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq9725 eq46956
    | exact resolve eq46956 eq9725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9725 eq46956
  have eq47090 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq47044
       have i₂ := eq37015
       grind)
    | exact superpose eq37015 eq47044
    | exact resolve eq47044 eq37015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37015 eq47044
  have eq47128 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) = (M.op (σ y) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq47090 eq681
    | exact resolve eq681 eq47090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq47090
  have eq47185 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq193 eq47128
    | exact resolve eq47128 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq47128
  have eq47277 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq47185 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq47185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47279 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq47185 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq47185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47185
  have eq47315 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq42619 eq47279
    | exact resolve eq47279 eq42619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47279
  have eq47316 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq42619 eq47277
    | exact resolve eq47277 eq42619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42619 eq47277
  have eq47331 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq47316
       have r₂ := eq47315
       grind)
    | exact resolve eq47316 eq47315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47315 eq47316
  have eq47441 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq47331 eq116
    | exact resolve eq116 eq47331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq47331
  have eq55488 : (M.op y y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq37052 eq661
    | (have j0 := eq661 y (M.op (M.op x y) y)
       grind)
    | exact resolve eq661 eq37052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55713 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq37047 eq55488
    | exact resolve eq55488 eq37047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55488
  have eq55740 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq28 eq55713
    | (have j1 := eq28 y (M.op x y)
       grind)
    | exact resolve eq55713 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55713
  have eq55746 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq37052 eq55740
    | exact resolve eq55740 eq37052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55740
  have eq55799 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op x y))) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1016 X1 X0 y
       have i₂ := eq55746
       grind)
    | exact superpose eq55746 eq1016
    | exact resolve eq1016 eq55746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016 eq55746
  have eq55881 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq9663 eq55799
    | exact resolve eq55799 eq9663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9663 eq55799
  have eq55901 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq37052 eq55881
    | exact resolve eq55881 eq37052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37052 eq55881
  have eq55916 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq37047 eq55901
    | exact resolve eq55901 eq37047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55901
  have eq55917 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq55916
  have eq55976 : (M.op y y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55917 eq661
    | (have j0 := eq661 y (M.op (M.op x y) y)
       grind)
    | exact resolve eq661 eq55917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq55988 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37047 eq55976
    | exact resolve eq55976 eq37047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37047 eq55976
  have eq56362 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55988 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq55988
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq55988
       grind)
    | exact resolve eq13 eq55988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56400 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq56362
  have eq56423 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55917 eq56400
    | exact resolve eq56400 eq55917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56400
  have eq56424 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq56423
  have eq56479 : y = (M.op y (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq594 y
       have i₂ := eq56424
       grind)
    | exact superpose eq56424 eq594
    | exact resolve eq594 eq56424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq56528 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq56424
       grind)
    | exact superpose eq56424 eq28
    | exact resolve eq28 eq56424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56424
  have eq56565 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq56528
  have eq56581 : y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55917 eq56479
    | exact resolve eq56479 eq55917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55917 eq56479
  have eq56595 : y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55988 eq56581
    | exact resolve eq56581 eq55988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55988 eq56581
  have eq56596 : y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq56595
  have eq56608 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq47441
       have i₂ := eq56565
       grind)
    | exact superpose eq56565 eq47441
    | exact resolve eq47441 eq56565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47441 eq56565
  have eq56627 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56596 eq56608
    | exact resolve eq56608 eq56596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56596 eq56608
  have eq56628 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq56627
  have eq56653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56628 eq14
    | exact resolve eq14 eq56628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56628
  have eq56669 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq56653
    | exact resolve eq56653 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56653
  have eq56677 : y = (M.op x y) := by
    first
    | (have r₁ := eq56669
       have r₂ := eq27
       grind)
    | exact resolve eq56669 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56669
  have eq56684 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq56677
       grind)
    | exact superpose eq56677 eq24
    | exact resolve eq24 eq56677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq56892 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq37408
       have i₂ := eq56677
       grind)
    | exact superpose eq56677 eq37408
    | (have r₁ := eq37408
       have r₂ := eq56677
       grind)
    | exact resolve eq37408 eq56677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37408 eq56677
  have eq56901 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq56892
  have eq56938 : (σ x) = (σ y) := by
    first
    | exact superpose eq37048 eq56684
    | exact resolve eq56684 eq37048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37048 eq56684
  have eq56944 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq56938 eq26
    | exact resolve eq26 eq56938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq56938
  have eq57537 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq56901 eq37050
    | exact resolve eq37050 eq56901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37050 eq56901
  have eq57566 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq57537
    | exact resolve eq57537 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq57537
  have eq57575 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq37249 eq57566
    | exact resolve eq57566 eq37249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57566
  have eq57696 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56944 eq28
    | exact resolve eq28 eq56944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq56944
  have eq57744 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57575 eq57696
    | exact resolve eq57696 eq57575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57575 eq57696
  have eq57745 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq57744
  have eq57868 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq57745 eq27
    | exact resolve eq27 eq57745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq57745
  have eq58053 : False := by grind
  exact eq58053

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pyx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq66 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq57 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq57
    | exact resolve eq57 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq111 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq111 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq111
    | (have j0 := eq111 (σ X0) (σ X1)
       grind)
    | exact resolve eq111 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = X2 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 X0
       have i₂ := eq111 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq111 X0 (M.op X2 X1)
       grind)
    | exact superpose eq111 eq9
    | (have j1 := eq111 X0 X1
       grind)
    | exact resolve eq9 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0
       have i₂ := eq111 X0 X1
       grind)
    | (have i₁ := eq59 X0
       have i₂ := eq111 X0 (M.op X0 X0)
       grind)
    | exact superpose eq111 eq59
    | (have j1 := eq111 X0 X1
       grind)
    | exact resolve eq59 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq127 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq111 X0 (τ X1)
       grind)
    | exact superpose eq111 eq19
    | (have j1 := eq111 X0 (τ X1)
       grind)
    | exact resolve eq19 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq111
  have eq153 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f153_11 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
      intro X0 X1
      grind
    have f153_12 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
      intro X0 X1
      grind
    have f153_20 : X0 ≠ (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) := by grind
    have f153_83 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f153_11 X0 (M.op X1 (M.op X1 X1))
         have i₂ := f153_12 X1 X1
         grind)
      | exact superpose f153_12 f153_11
      | exact resolve f153_11 f153_12
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f153_137 : X0 ≠ X0 := by
      first
      | (have i₁ := f153_20
         have i₂ := f153_83 X0 X1
         grind)
      | exact superpose f153_83 f153_20
      | (have r₁ := f153_20
         have r₂ := f153_83 X0 X1
         grind)
      | exact resolve f153_20 f153_83
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f153_140 : False := by grind
    exact f153_140
  clear eq66 eq84
  have eq156 : ∀ X1 X3 X4 : G, (M.op (M.op X1 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X1 X3 X4
    first
    | (have i₁ := eq30 X3 x (M.op (M.op x x) (M.op X1 X1)) X4
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq312 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq118 X1 X0 X0
       have i₂ := eq121 X0 X0
       grind)
    | exact superpose eq121 eq118
    | (have j0 := eq118 X1 X0 x
       have j1 := eq121 X1 X0
       grind)
    | exact resolve eq118 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq121
  have eq324 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq312 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq312 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq312 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq484 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq114 X0 X1
       grind)
    | exact superpose eq114 eq10
    | (have j1 := eq114 X0 X1
       grind)
    | exact resolve eq10 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq538 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq324 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq539 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq543 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq539 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq539
    | exact resolve eq539 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq543 X0
       have i₂ := eq539 X0
       grind)
    | exact superpose eq539 eq543
    | exact resolve eq543 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq543
  have eq1367 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 (M.op X0 X0) X2 X1
       have i₂ := eq153 X0 X0
       grind)
    | exact superpose eq153 eq62
    | exact resolve eq62 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq1370 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq62 X0 X0 x (M.op X0 X0)
       have i₂ := eq156 x X0 X0
       grind)
    | exact superpose eq156 eq62
    | exact resolve eq62 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq1417 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1370 (σ X0)
       have i₂ := eq546 X0
       grind)
    | exact superpose eq546 eq1370
    | exact resolve eq1370 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1603 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op X0 X1) X1 X3 X2
       have i₂ := eq1367 X1 X1 X0
       grind)
    | exact superpose eq1367 eq62
    | exact resolve eq62 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq1623 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1603 X0 X1 x x
       have i₂ := eq62 X1 X1 x x
       grind)
    | exact superpose eq62 eq1603
    | exact resolve eq1603 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1603
  have eq1989 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq127
    | exact resolve eq127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq2113 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1989 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1989
    | (have j0 := eq1989 X0 X1
       grind)
    | exact resolve eq1989 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989
  have eq4645 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 X1
       have i₂ := eq546 X0
       grind)
    | exact superpose eq546 eq484
    | (have j0 := eq484 X0 X1
       grind)
    | exact resolve eq484 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484 eq546
  have eq4646 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4645 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4645
    | (have j0 := eq4645 X0 X1
       grind)
    | exact resolve eq4645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645
  have eq4814 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4646 y x
       grind)
    | exact superpose eq4646 eq16
    | (have j1 := eq4646 y x
       grind)
    | exact resolve eq16 eq4646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4646
  have eq4847 : x = (M.op y y) := by
    first
    | (have j1 := eq2113 x y
       grind)
    | (have r₁ := eq4814
       have r₂ := eq2113 x y
       grind)
    | exact resolve eq4814 eq2113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113 eq4814
  have eq4887 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1417 y
       have i₂ := eq4847
       grind)
    | exact superpose eq4847 eq1417
    | exact resolve eq1417 eq4847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq4914 : x = (M.op x y) := by
    first
    | (have i₁ := eq1623 y y
       have i₂ := eq4847
       grind)
    | exact superpose eq4847 eq1623
    | exact resolve eq1623 eq4847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623 eq4847
  have eq5706 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4887
       grind)
    | exact superpose eq4887 eq16
    | exact resolve eq16 eq4887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4887
  have eq5743 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq5706
       have i₂ := eq4914
       grind)
    | exact superpose eq4914 eq5706
    | exact resolve eq5706 eq4914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4914 eq5706
  have eq5744 : False := by grind
  exact eq5744

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_pyy_pyx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
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
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
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
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq33 X0 (k X0 X0)
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq33 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq38 X0 (k X0 X0)
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq38 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq46
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq52 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq123 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq127 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq123 X0 X1
       have j1 := eq56 X1 X0
       grind)
    | (have r₁ := eq123 X1 X1
       have r₂ := eq56 X1 X1
       grind)
    | (have r₁ := eq123 X1 X0
       have r₂ := eq56 X0 X1
       grind)
    | exact resolve eq123 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq123
  have eq286 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq127 (σ X1) (σ X0)
       grind)
    | exact superpose eq127 eq15
    | exact resolve eq15 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq127 X1 X0
       grind)
    | exact superpose eq127 eq286
    | exact resolve eq286 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq286
  have eq295 : False := by grind
  exact eq295

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pxy_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq30 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq56
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq56
    | exact resolve eq56 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq59 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq86 : ∀ X0 X1 X2 : G, (τ X0) = (M.op X2 (M.op (M.op X1 X2) (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X2 X1
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq94 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq9
    | exact resolve eq9 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq94 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq94
    | exact resolve eq94 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq170 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X2 X3) (M.op X0 X1))) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X3 X2
       have i₂ := eq126 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq126 X1 X1
       grind)
    | exact superpose eq126 eq9
    | (have j1 := eq126 X0 X1
       grind)
    | exact resolve eq9 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq132 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq116 X1 X1
       grind)
    | exact superpose eq116 eq132
    | exact resolve eq132 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq132
  have eq768 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq170 X0 X1 X0 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq170
    | (have j0 := eq170 X0 X1 x x
       grind)
    | exact resolve eq170 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq170
  have eq2070 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq103 X0 (M.op X0 X0) X2 X1
       have i₂ := eq294 X0 X0
       grind)
    | exact superpose eq294 eq103
    | exact resolve eq103 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2544 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq98 X1
       have i₂ := eq2070 X1 X2 X0
       grind)
    | exact superpose eq2070 eq98
    | exact resolve eq98 eq2070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2546 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq294 X1 X3
       have i₂ := eq2070 X1 X2 X0
       grind)
    | exact superpose eq2070 eq294
    | exact resolve eq294 eq2070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq2577 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq103 (M.op X0 X1) X1 X3 X2
       have i₂ := eq2070 X1 X1 X0
       grind)
    | exact superpose eq2070 eq103
    | exact resolve eq103 eq2070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070
  have eq2603 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2577 X0 X1 x x
       have i₂ := eq103 X1 X1 x x
       grind)
    | exact superpose eq103 eq2577
    | exact resolve eq2577 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq2577
  have eq4397 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) = (M.op (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2544 X0 (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) (M.op X1 X2)
       have i₂ := eq2546 X3 X2 (M.op X0 (M.op X1 X2)) X1
       grind)
    | exact superpose eq2546 eq2544
    | exact resolve eq2544 eq2546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544 eq2546
  have eq4430 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4397 X0 X1 X2 X3
       have i₂ := eq2603 (M.op X3 (M.op X0 (M.op X1 X2))) X2
       grind)
    | exact superpose eq2603 eq4397
    | exact resolve eq4397 eq2603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603 eq4397
  have eq5918 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4430 X1 X0 X1 X1
       have i₂ := eq768 X0 X1
       grind)
    | exact superpose eq768 eq4430
    | (have j1 := eq768 X0 X1
       grind)
    | exact resolve eq4430 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4430
  have eq13716 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq126 X0 X1
       have i₂ := eq5918 X0 X1
       grind)
    | (have i₁ := eq126 X1 X1
       have i₂ := eq5918 X0 X1
       grind)
    | exact superpose eq5918 eq126
    | (have j0 := eq126 X0 X1
       have j1 := eq5918 X0 X1
       grind)
    | exact resolve eq126 eq5918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq13737 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X1 X1))) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq768 X0 X1
       have i₂ := eq5918 X0 X1
       grind)
    | (have i₁ := eq768 X1 X1
       have i₂ := eq5918 X0 X1
       grind)
    | exact superpose eq5918 eq768
    | (have j0 := eq768 X0 X1
       have j1 := eq5918 X0 X1
       grind)
    | exact resolve eq768 eq5918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq5918
  have eq13804 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X1 X1))) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13737 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13737
  have eq13816 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13716 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13716
  have eq13827 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13804 X0 X1
       have i₂ := eq98 X1
       grind)
    | exact superpose eq98 eq13804
    | (have j0 := eq13804 X0 X1
       grind)
    | exact resolve eq13804 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq13804
  have eq14378 : ∀ X0 X1 X2 X3 : G, (τ X1) = (M.op X2 (M.op (M.op X3 X2) (τ (M.op X0 X0)))) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq86 X1 X3 X2
       have i₂ := eq13816 X0 X1
       grind)
    | (have i₁ := eq86 X0 X1 X2
       have i₂ := eq13816 X0 X1
       grind)
    | exact superpose eq13816 eq86
    | (have j1 := eq13816 X0 X1
       grind)
    | exact resolve eq86 eq13816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13816
  have eq14516 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14378 X0 X1 x x
       have i₂ := eq86 X0 x x
       grind)
    | exact superpose eq86 eq14378
    | (have j0 := eq14378 X0 X1 x x
       grind)
    | exact resolve eq14378 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq14378
  have eq14578 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14516 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14516
    | (have j0 := eq14516 (σ X0) (σ X1)
       grind)
    | exact resolve eq14516 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14516
  have eq14626 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14578 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq14578
    | (have j0 := eq14578 X0 X1
       grind)
    | exact resolve eq14578 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14578
  have eq14638 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14626 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14626
    | (have j0 := eq14626 X0 X1
       grind)
    | exact resolve eq14626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14626
  have eq14892 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq14638 y x
       grind)
    | exact superpose eq14638 eq16
    | (have j1 := eq14638 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq14638 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq14638 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq14638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14638
  have eq15005 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq14892
       have i₂ := eq13827 y x
       grind)
    | exact superpose eq13827 eq14892
    | (have j1 := eq13827 x y
       grind)
    | (have r₁ := eq14892
       have r₂ := eq13827 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq14892
       have r₂ := eq13827 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq14892 eq13827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13827 eq14892
  have eq15010 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by grind
  clear eq15005
  have eq15011 : x = y := by grind
  clear eq15010
  have eq15028 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15011
       grind)
    | exact superpose eq15011 eq16
    | exact resolve eq16 eq15011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15011
  have eq15029 : False := by grind
  exact eq15029

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyy_pyx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq18
    | exact resolve eq18 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq83
    | exact resolve eq83 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq83
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq10
    | exact resolve eq10 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq179 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq218 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq9
    | exact resolve eq9 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq628 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq179
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq179
    | exact resolve eq179 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq629 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq628
       have i₂ := eq95 y
       grind)
    | exact superpose eq95 eq628
    | exact resolve eq628 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq657 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq629
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq629
    | (have j1 := eq56 x y
       grind)
    | exact resolve eq629 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq629
  have eq658 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq657
  have eq8080 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq10
    | exact resolve eq10 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq8127 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq8080
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq8080
    | exact resolve eq8080 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8080
  have eq8128 : (M.op x x) = (M.op y y) := by grind
  clear eq8127
  have eq8159 : ∀ X0 : G, y = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq218 X0 y
       have i₂ := eq8128
       grind)
    | exact superpose eq8128 eq218
    | exact resolve eq218 eq8128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8128
  have eq8245 : x = y := by
    first
    | (have i₁ := eq8159 x
       have i₂ := eq218 x x
       grind)
    | exact superpose eq218 eq8159
    | exact resolve eq8159 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq8159
  have eq8259 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8245
       grind)
    | exact superpose eq8245 eq16
    | exact resolve eq16 eq8245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8245
  have eq8260 : False := by grind
  exact eq8260
