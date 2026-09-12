import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq64 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq64 X1 X0 X3
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq84 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq84 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq84 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq84 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq86 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq44
    | exact resolve eq44 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq87 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq15
    | exact resolve eq15 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq85 (σ X0)
       grind)
    | exact superpose eq85 eq87
    | exact resolve eq87 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq89 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq85 (τ X0)
       grind)
    | exact superpose eq85 eq86
    | exact resolve eq86 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq86
  have eq97 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq16
    | (have j1 := eq97 x y
       grind)
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq129 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq103
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq103
       have r₂ := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq103 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq130 : y = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq129
  have eq149 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq77 x X2 X0 X1
       grind)
    | exact superpose eq77 eq9
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq181 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq149 x X1 X0
       grind)
    | exact superpose eq149 eq9
    | exact resolve eq9 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq2953 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq88 y
       have i₂ := eq130
       grind)
    | exact superpose eq130 eq88
    | exact resolve eq88 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq2979 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq2953
  have eq2988 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq2979
       grind)
    | exact superpose eq2979 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq2979
       grind)
    | exact resolve eq12 eq2979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2992 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq89 (σ y)
       have i₂ := eq2979
       grind)
    | exact superpose eq2979 eq89
    | exact resolve eq89 eq2979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2979
  have eq3017 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2988 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2988
  have eq3023 : y = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2992
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2992
    | exact resolve eq2992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992
  have eq3024 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq3023
       grind)
    | exact superpose eq3023 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq3023
       grind)
    | exact resolve eq12 eq3023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3023
  have eq3053 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3024 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3024
  have eq3060 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq3053 X0
       grind)
    | exact superpose eq3053 eq15
    | exact resolve eq15 eq3053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3053
  have eq11106 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3060 x
       grind)
    | exact superpose eq3060 eq16
    | exact resolve eq16 eq3060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3060
  have eq11115 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq11106
       have r₂ := eq3017 (σ x)
       grind)
    | exact resolve eq11106 eq3017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017 eq11106
  have eq11136 : (M.op (τ (σ y)) (τ (σ y))) = (τ (M.op (σ x) (σ x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq89 (σ y)
       have i₂ := eq11115
       grind)
    | exact superpose eq11115 eq89
    | exact resolve eq89 eq11115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11115
  have eq11168 : (M.op (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq11136
       have i₂ := eq89 (σ x)
       grind)
    | exact superpose eq89 eq11136
    | exact resolve eq11136 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11136
  have eq11171 : (M.op x x) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq11168
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11168
    | exact resolve eq11168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11168
  have eq11173 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq11171
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq11171
    | exact resolve eq11171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11171
  have eq11174 : (M.op x x) = (M.op y y) := by grind
  clear eq11173
  have eq11261 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq11174
       grind)
    | exact superpose eq11174 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq11174
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq11174
       grind)
    | exact resolve eq13 eq11174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11263 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq88 y
       have i₂ := eq11174
       grind)
    | exact superpose eq11174 eq88
    | exact resolve eq88 eq11174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11297 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11263
       have i₂ := eq88 x
       grind)
    | exact superpose eq88 eq11263
    | exact resolve eq11263 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11263
  have eq11512 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq13 (σ y) X0
       have i₂ := eq11297
       grind)
    | exact superpose eq11297 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq11297
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq11297
       grind)
    | exact resolve eq13 eq11297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11297
  have eq11685 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq11261 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11261
  have eq11698 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq11685
       grind)
    | exact superpose eq11685 eq15
    | exact resolve eq15 eq11685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11685
  have eq11718 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11698
       grind)
    | exact superpose eq11698 eq16
    | exact resolve eq16 eq11698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11698
  have eq13023 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11718
       have i₂ := eq11512 (σ x)
       grind)
    | exact superpose eq11512 eq11718
    | (have j1 := eq11512 (σ x)
       grind)
    | (have r₁ := eq11718
       have r₂ := eq11512 (σ x)
       grind)
    | exact resolve eq11718 eq11512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11512 eq11718
  have eq13028 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq13023
  have eq13049 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq89 (σ x)
       have i₂ := eq13028
       grind)
    | exact superpose eq13028 eq89
    | exact resolve eq89 eq13028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq13028
  have eq13079 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13049
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13049
    | exact resolve eq13049 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13049
  have eq13080 : x = (M.op x x) := by grind
  clear eq13079
  have eq13108 : x = (M.op y y) := by
    first
    | (have i₁ := eq11174
       have i₂ := eq13080
       grind)
    | exact superpose eq13080 eq11174
    | exact resolve eq11174 eq13080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11174 eq13080
  have eq13231 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq88 y
       have i₂ := eq13108
       grind)
    | exact superpose eq13108 eq88
    | exact resolve eq88 eq13108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq13236 : x = (M.op x y) := by
    first
    | (have i₁ := eq181 y y
       have i₂ := eq13108
       grind)
    | exact superpose eq13108 eq181
    | exact resolve eq181 eq13108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13108
  have eq13260 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13236
       grind)
    | exact superpose eq13236 eq16
    | exact resolve eq16 eq13236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13236
  have eq13637 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq181 (σ y) (σ y)
       have i₂ := eq13231
       grind)
    | exact superpose eq13231 eq181
    | exact resolve eq181 eq13231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq13231
  have eq13661 : False := by grind
  exact eq13661

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation450 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law450 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq40 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq16
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq959 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq191 (τ X1) (τ X0)
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq191
    | (have j0 := eq191 (τ X1) (τ X0)
       grind)
    | exact resolve eq191 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq974 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq959 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq959
    | (have j0 := eq959 X0 X1
       grind)
    | exact resolve eq959 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq980 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq974 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq974
    | (have j0 := eq974 X0 X1
       grind)
    | exact resolve eq974 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq985 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq980 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq980
    | (have j0 := eq980 X0 X1
       grind)
    | exact resolve eq980 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq989 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq985 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq985
    | (have j0 := eq985 X0 X1
       grind)
    | exact resolve eq985 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq992 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq989
    | (have j0 := eq989 X0 X1
       grind)
    | exact resolve eq989 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq993 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq992 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq992
    | (have j0 := eq992 X0 X1
       grind)
    | exact resolve eq992 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq5848 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq78 X1 X0
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq78 (σ X1) X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5887 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq78 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq5888 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5887 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5887
  have eq5890 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5848 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5848
  have eq5891 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5890 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5890
  have eq5893 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5888 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5888
    | (have j0 := eq5888 X0
       grind)
    | exact resolve eq5888 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5888
  have eq5933 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq44 X0
       have i₂ := eq5893 X0
       grind)
    | exact superpose eq5893 eq44
    | (have j1 := eq5893 X0
       grind)
    | exact resolve eq44 eq5893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5893
  have eq5967 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5933 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5933
    | (have j0 := eq5933 X0
       grind)
    | exact resolve eq5933 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5933
  have eq5968 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5967 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5967
  have eq5970 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5968 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5968
    | exact resolve eq5968 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5997 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq5968 X0
       grind)
    | exact superpose eq5968 eq11
    | exact resolve eq11 eq5968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6059 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5970 X0
       have i₂ := eq40 X0 X0
       grind)
    | exact superpose eq40 eq5970
    | exact resolve eq5970 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5970
  have eq6195 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq6059 X0
       grind)
    | exact superpose eq6059 eq11
    | exact resolve eq11 eq6059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6304 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6195 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq6195
    | exact resolve eq6195 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6195
  have eq6368 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0 X0
       have i₂ := eq6304 (τ X0)
       grind)
    | exact superpose eq6304 eq40
    | exact resolve eq40 eq6304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6424 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6368 X0
       have i₂ := eq6059 X0
       grind)
    | exact superpose eq6059 eq6368
    | exact resolve eq6368 eq6059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6059 eq6368
  have eq7000 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq7062 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq7000 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq7000
    | exact resolve eq7000 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7000
  have eq7098 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq7062 X0
       have i₂ := eq6304 X0
       grind)
    | exact superpose eq6304 eq7062
    | exact resolve eq7062 eq6304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7062
  have eq7118 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq7098
  have eq58253 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5891 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5891
    | exact resolve eq5891 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58309 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq5891 X0 X1
       grind)
    | exact superpose eq5891 eq37
    | (have j1 := eq5891 X0 X1
       grind)
    | exact resolve eq37 eq5891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq5891
  have eq58527 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq58309 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58309
    | (have j0 := eq58309 X0 X1
       grind)
    | exact resolve eq58309 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58309
  have eq58558 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq58253 X0 X1
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq58253
    | (have j0 := eq58253 X0 X1
       grind)
    | exact resolve eq58253 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58253
  have eq58932 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq58558 X1 X0
       grind)
    | exact superpose eq58558 eq11
    | (have j1 := eq58558 X1 X0
       grind)
    | exact resolve eq11 eq58558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58558
  have eq59148 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58932 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq58932
    | (have j0 := eq58932 X0 X1
       grind)
    | exact resolve eq58932 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58932
  have eq60252 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq59148 (τ X0) X1
       grind)
    | exact superpose eq59148 eq19
    | (have j1 := eq59148 (τ X0) X1
       grind)
    | exact resolve eq19 eq59148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq59148
  have eq60502 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60252 X0 X1
       have i₂ := eq6424 X0
       grind)
    | exact superpose eq6424 eq60252
    | (have j0 := eq60252 X0 X1
       grind)
    | exact resolve eq60252 eq6424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6424 eq60252
  have eq60892 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq58527 (τ X1) X0
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq58527
    | (have j0 := eq58527 (τ X0) X1
       grind)
    | exact resolve eq58527 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq58527
  have eq61146 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq60892 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60892
    | (have j0 := eq60892 X0 X1
       grind)
    | exact resolve eq60892 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60892
  have eq61236 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61146 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61146
    | (have j0 := eq61146 X0 X1
       grind)
    | exact resolve eq61146 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61146
  have eq62541 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq61236 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61236
  have eq68745 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq60502 X1 (τ X0)
       grind)
    | exact superpose eq60502 eq18
    | (have j1 := eq60502 X1 (τ X0)
       grind)
    | exact resolve eq18 eq60502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq60502
  have eq68851 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq68745 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq68745
    | (have j0 := eq68745 X0 X1
       grind)
    | exact resolve eq68745 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68745
  have eq68953 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq68851 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq68851
    | (have j0 := eq68851 X0 X1
       grind)
    | exact resolve eq68851 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68851
  have eq69038 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (k X0 X1) = X0 ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq68953 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq68953
    | (have j0 := eq68953 X0 X1
       grind)
    | exact resolve eq68953 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68953
  have eq75508 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq69038 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq69038
    | (have j0 := eq69038 X1 (σ X0)
       grind)
    | exact resolve eq69038 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69038
  have eq75825 : ∀ X0 X1 : G, (τ X1) = (k X0 X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75508 X0 X1
       have i₂ := eq5968 X0
       grind)
    | exact superpose eq5968 eq75508
    | (have j0 := eq75508 X0 X1
       grind)
    | exact resolve eq75508 eq5968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5968 eq75508
  have eq75907 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75825 X0 X1
       have i₂ := eq6304 X0
       grind)
    | exact superpose eq6304 eq75825
    | (have j0 := eq75825 X0 X1
       grind)
    | exact resolve eq75825 eq6304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75825
  have eq79781 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75907 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75907
    | (have j0 := eq75907 X1 (σ X0)
       grind)
    | exact resolve eq75907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75907
  have eq80077 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79781 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq79781
    | (have j0 := eq79781 X0 X1
       grind)
    | exact resolve eq79781 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79781
  have eq80160 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq80077 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq80077
    | (have j0 := eq80077 X0 X1
       grind)
    | exact resolve eq80077 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80077
  have eq80439 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq183
       have i₂ := eq80160 y x
       grind)
    | exact superpose eq80160 eq183
    | (have j1 := eq80160 y x
       grind)
    | (have r₁ := eq183
       have r₂ := eq80160 y x
       grind)
    | exact resolve eq183 eq80160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq80160
  have eq80552 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x x) := by grind
  clear eq80439
  have eq80618 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq191 x y
       grind)
    | (have r₁ := eq80552
       have r₂ := eq191 x y
       grind)
    | exact resolve eq80552 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq80552
  have eq80760 : (σ y) = (σ (k x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80618
       have i₂ := eq5997 x
       grind)
    | exact superpose eq5997 eq80618
    | exact resolve eq80618 eq5997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80618
  have eq80854 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80760
       have i₂ := eq6304 x
       grind)
    | exact superpose eq6304 eq80760
    | exact resolve eq80760 eq6304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80760
  have eq82222 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80854
       grind)
    | exact superpose eq80854 eq16
    | exact resolve eq16 eq80854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82267 : (τ (σ y)) ≠ (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq62541 (σ y) (σ x)
       have i₂ := eq80854
       grind)
    | exact superpose eq80854 eq62541
    | (have j0 := eq62541 (σ y) (σ x)
       grind)
    | exact resolve eq62541 eq80854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62541 eq80854
  have eq82270 : (σ y) = (M.op (σ x) (σ x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq82267
  have eq82276 : (σ y) = (σ (k x x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82270
       have i₂ := eq5997 x
       grind)
    | exact superpose eq5997 eq82270
    | exact resolve eq82270 eq5997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5997 eq82270
  have eq82299 : (σ y) = (σ (M.op x x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82276
       have i₂ := eq6304 x
       grind)
    | exact superpose eq6304 eq82276
    | exact resolve eq82276 eq6304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6304 eq82276
  have eq82300 : (σ y) = (σ (M.op x x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ y = (M.op x x) := by grind
  clear eq82299
  have eq82322 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82300
       have i₂ := eq30 (σ y) x
       grind)
    | exact superpose eq30 eq82300
    | exact resolve eq82300 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq82300
  have eq82325 : y = (k y x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82322
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq82322
    | exact resolve eq82322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82322
  have eq83008 : y ≠ y ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq993 y x
       have i₂ := eq82325
       grind)
    | exact superpose eq82325 eq993
    | (have j0 := eq993 y x
       grind)
    | (have r₁ := eq993 y x
       have r₂ := eq82325
       grind)
    | exact resolve eq993 eq82325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993 eq82325
  have eq83022 : y ≠ y ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq83008
  have eq83023 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq83022
  have eq83972 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq82222
       have i₂ := eq83023
       grind)
    | exact superpose eq83023 eq82222
    | exact resolve eq82222 eq83023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82222 eq83023
  have eq83973 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq83972
  have eq83974 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq83973
  have eq84614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7118 x
       have i₂ := eq83974
       grind)
    | exact superpose eq83974 eq7118
    | exact resolve eq7118 eq83974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83974
  have eq84703 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq84614
       have r₂ := eq16
       grind)
    | exact resolve eq84614 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84614
  have eq84734 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq84703
       grind)
    | exact superpose eq84703 eq10
    | exact resolve eq10 eq84703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84703
  have eq84918 : y = (M.op x x) := by
    first
    | (have i₁ := eq84734
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq84734
    | exact resolve eq84734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84734
  have eq86459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7118 x
       have i₂ := eq84918
       grind)
    | exact superpose eq84918 eq7118
    | exact resolve eq7118 eq84918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7118 eq84918
  have eq86548 : False := by grind
  exact eq86548

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation452 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law452 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq2854 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2901 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2854 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2854
  have eq2902 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2901 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2901
  have eq3362 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2902 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2902
  have eq3365 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3362 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq3362 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq3362 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq3362 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq3362 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3362
  have eq3474 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq3365 X1 (τ X0)
       grind)
    | exact superpose eq3365 eq19
    | (have j1 := eq3365 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq3365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3477 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3365 (σ X1) (σ X0)
       grind)
    | exact superpose eq3365 eq15
    | (have j1 := eq3365 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq3365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq3630 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3474 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3474
    | exact resolve eq3474 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474
  have eq3733 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3630 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3630
    | (have j0 := eq3630 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq3630 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3630
  have eq3927 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3477 x y
       grind)
    | exact superpose eq3477 eq16
    | (have j1 := eq3477 x y
       grind)
    | exact resolve eq16 eq3477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3477
  have eq3983 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3927
       have i₂ := eq3733 x y
       grind)
    | exact superpose eq3733 eq3927
    | (have j1 := eq3733 (σ x) (σ y)
       grind)
    | (have r₁ := eq3927
       have r₂ := eq3733 x y
       grind)
    | (have r₁ := eq3927
       have r₂ := eq3733 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3927
       have r₂ := eq3733 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3927 eq3733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3733 eq3927
  have eq3984 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3983
  have eq3988 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3984
       grind)
    | exact superpose eq3984 eq10
    | exact resolve eq10 eq3984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3984
  have eq4032 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3988
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3988
    | exact resolve eq3988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3988
  have eq4033 : x = y := by grind
  clear eq4032
  have eq4035 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4033
       grind)
    | exact superpose eq4033 eq16
    | exact resolve eq16 eq4033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4033
  have eq4036 : False := by grind
  exact eq4036

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pxy_pxx_pxy_Equation4521 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
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
  have eq52 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X4) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 X0 x x X4
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X3) (M.op X4 X5)) = (M.op (M.op X0 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 (M.op X0 X3) X4 X5 X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 X1 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X3 X4 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) ≠ X0 ∨ (M.op (M.op X0 X1) X1) = (k X0 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op X0 (M.op X1 X2)) (M.op X1 X2)
       have r₂ := eq14 X0 X1 X2 (M.op X1 X2)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 X3) ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X3) X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op X0 (M.op X1 X2)) (M.op X1 X2)
       have r₂ := eq14 X0 X1 X2 (M.op X1 X2)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq74
    | (have j0 := eq74 X0 (σ X1)
       grind)
    | exact resolve eq74 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq44
    | (have j1 := eq74 x y
       grind)
    | exact resolve eq44 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq109 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq16
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) X2) X2) ∨ (M.op X3 (M.op X0 X1)) = X3 ∨ (k X3 (M.op X0 X1)) = (M.op X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X3 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : (σ (k (k x x) x)) = (k (k (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq39 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq39
    | exact resolve eq39 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq209 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq57 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq57
    | (have j0 := eq57 x y
       grind)
    | exact resolve eq57 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 (σ x) (σ y)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (σ x) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (σ x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq13
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : (M.op (σ x) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq224 eq227
    | exact resolve eq227 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq259 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq294 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq334 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op (M.op X0 X1) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op X0 X2) X2 X3
       have i₂ := eq52 X0 X2 X1
       grind)
    | (have i₁ := eq52 (M.op X0 X2) X2 X3
       have i₂ := eq52 X0 X1 X2
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
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
  have eq380 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq224 eq357
    | exact resolve eq357 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq396 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 x y X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 X0 X1 X2 x y
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq906 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq396 X0 x x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq396
    | (have j1 := eq14 X0 x y X1
       grind)
    | exact resolve eq396 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq984 : ∀ X0 X3 X4 X5 : G, (M.op (M.op X0 X3) (M.op X4 X5)) = (M.op (M.op X0 (M.op x y)) X3) := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq55 X0 x x X3 X4 X5
       have i₂ := eq396 X0 x x
       grind)
    | (have i₁ := eq55 X0 x y X3 X4 X5
       have i₂ := eq396 X0 x x
       grind)
    | exact superpose eq396 eq55
    | (have j0 := eq55 X0 x y X3 X4 X5
       grind)
    | exact resolve eq55 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq985 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op x y)) X3) = (M.op (M.op X0 X3) (M.op x y)) := by
    intro X0 X3
    first
    | (have i₁ := eq984 X0 X3 x x
       have i₂ := eq396 (M.op X0 X3) x x
       grind)
    | (have i₁ := eq984 X0 X3 x y
       have i₂ := eq396 (M.op X0 X3) x x
       grind)
    | exact superpose eq396 eq984
    | (have j0 := eq984 X0 X3 x y
       grind)
    | exact resolve eq984 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq1214 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op X1 X2)) ≠ X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X4 X5)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq69 X0 x X2 x
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq69
    | exact resolve eq69 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq1233 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op x y)) ≠ X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X4 X5)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq1214 X0 X1 X2 X4 X5
       have i₂ := eq396 X0 X1 X2
       grind)
    | (have i₁ := eq1214 X0 x y X4 X5
       have i₂ := eq396 X0 X1 X2
       grind)
    | exact superpose eq396 eq1214
    | (have j0 := eq1214 X0 x y X4 X5
       grind)
    | exact resolve eq1214 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1263 : ∀ X0 X4 X5 : G, (M.op X0 (M.op x y)) = (k X0 (M.op X4 X5)) ∨ (M.op X0 (M.op x y)) ≠ X0 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq1233 X0 x x X4 X5
       have i₂ := eq396 X0 x x
       grind)
    | (have i₁ := eq1233 X0 x y X4 X5
       have i₂ := eq396 X0 x x
       grind)
    | exact superpose eq396 eq1233
    | (have j0 := eq1233 X0 x y X4 X5
       grind)
    | exact resolve eq1233 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq1396 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (M.op X2 X3)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (σ X0) X2 X3 (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq14
    | (have j1 := eq88 X0 X1
       grind)
    | exact resolve eq14 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1411 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq88 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1421 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ X1)) = (M.op (σ X0) (M.op x y)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1396 X0 X1 x x
       have i₂ := eq396 (σ X0) x x
       grind)
    | (have i₁ := eq1396 X0 X1 x y
       have i₂ := eq396 (σ X0) X1 x
       grind)
    | exact superpose eq396 eq1396
    | (have j0 := eq1396 X0 X1 x y
       grind)
    | exact resolve eq1396 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1616 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) ≠ (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X0 X1 X2 X3
       have i₂ := eq396 X0 X1 X2
       grind)
    | (have i₁ := eq70 X0 x y X3
       have i₂ := eq396 X0 X1 X2
       grind)
    | exact superpose eq396 eq70
    | (have j0 := eq70 X0 x y X3
       grind)
    | (have r₁ := eq70 X0 X1 X2 (M.op x y)
       have r₂ := eq396 X0 X1 X2
       grind)
    | (have r₁ := eq70 X0 x y (M.op X1 X2)
       have r₂ := eq396 X0 X1 X2
       grind)
    | exact resolve eq70 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1617 : ∀ X0 X3 : G, (M.op X0 X3) ≠ (M.op X0 (M.op x y)) ∨ (k (M.op X0 X3) X3) = (M.op X0 (M.op x y)) := by
    intro X0 X3
    first
    | (have i₁ := eq1616 X0 x x X3
       have i₂ := eq396 X0 x x
       grind)
    | (have i₁ := eq1616 X0 x y X3
       have i₂ := eq396 X0 x x
       grind)
    | exact superpose eq396 eq1616
    | (have j0 := eq1616 X0 x y X3
       grind)
    | (have r₁ := eq1616 X0 x x (M.op x x)
       have r₂ := eq396 X0 x x
       grind)
    | (have r₁ := eq1616 X0 x x (M.op x y)
       have r₂ := eq396 X0 x y
       grind)
    | exact resolve eq1616 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616
  have eq1642 : (M.op (σ x) (M.op x y)) ≠ (M.op (σ x) (M.op x y)) ∨ (M.op (σ x) (M.op x y)) = (k (M.op (σ x) (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq242 eq1617
    | (have j0 := eq1617 (σ x) (M.op x y)
       grind)
    | (have r₁ := eq1617 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq242
       grind)
    | exact resolve eq1617 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq1617
  have eq1653 : (M.op (σ x) (M.op x y)) = (k (M.op (σ x) (M.op x y)) (M.op (σ x) (σ y))) := by grind
  clear eq1642
  have eq1740 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op x y)) ∨ (M.op X3 (M.op X0 X1)) = X3 ∨ (k X3 (M.op X0 X1)) = (M.op X3 X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq118 X0 X1 x X3
       have i₂ := eq906 (M.op X0 X1) x
       grind)
    | exact superpose eq906 eq118
    | (have j0 := eq118 X0 X1 x X3
       grind)
    | exact resolve eq118 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1741 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op x y)) ∨ (M.op X3 (M.op x y)) = X3 ∨ (k X3 (M.op X0 X1)) = (M.op X3 X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1740 X0 X1 X3
       have i₂ := eq396 X3 X0 X1
       grind)
    | (have i₁ := eq1740 x y X0
       have i₂ := eq396 X0 X1 x
       grind)
    | exact superpose eq396 eq1740
    | (have j0 := eq1740 X0 X1 X3
       grind)
    | exact resolve eq1740 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq1758 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq259 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq259
    | exact resolve eq259 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq1836 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 (M.op x y)) X1) ∨ (M.op X2 (M.op x y)) = X2 ∨ (k X2 (M.op X0 X1)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq985 eq1741
    | (have j0 := eq1741 X0 X1 X2
       grind)
    | exact resolve eq1741 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1842 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 (M.op x y)) ∨ (M.op X3 (M.op x y)) = X3 ∨ (M.op X3 X3) = (k X3 (M.op X0 (M.op x y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1741 X0 sF0 X3
       have i₂ := eq14 X0 X1 X2 sF0
       grind)
    | exact superpose eq14 eq1741
    | (have j0 := eq1741 X0 (M.op x y) X3
       grind)
    | (have r₁ := eq1741 X0 (M.op x y) X3
       have r₂ := eq14 X0 x y (M.op x y)
       grind)
    | exact resolve eq1741 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741
  have eq1848 : ∀ X0 X3 : G, (M.op X3 (M.op x y)) = X3 ∨ (M.op X3 X3) = (k X3 (M.op X0 (M.op x y))) := by
    intro X0 X3
    first
    | (have j0 := eq1842 X0 x x X3
       grind)
    | (have r₁ := eq1842 X0 x x X3
       have r₂ := eq396 X0 x x
       grind)
    | (have r₁ := eq1842 X0 x y X3
       have r₂ := eq396 X0 x y
       grind)
    | exact resolve eq1842 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842
  have eq1976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq103 eq74
    | (have j0 := eq74 x (σ y)
       grind)
    | exact resolve eq74 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq1977 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1976
    | exact resolve eq1976 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976
  have eq1980 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1977
       have r₂ := eq27
       grind)
    | exact resolve eq1977 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977
  have eq1986 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1980 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1980
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq1980
       grind)
    | exact resolve eq13 eq1980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980
  have eq2003 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1986
  have eq2023 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2003 eq109
    | exact resolve eq109 eq2003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq2003
  have eq2027 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq2023
    | exact resolve eq2023 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2023
  have eq2073 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74 y y
       have i₂ := eq2027
       grind)
    | exact superpose eq2027 eq74
    | (have j0 := eq74 x y
       grind)
    | exact resolve eq74 eq2027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2027
  have eq2074 : y = (M.op y y) := by grind
  clear eq2073
  have eq2078 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2074
       grind)
    | exact superpose eq2074 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq2074
       grind)
    | exact resolve eq13 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2085 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq2074
       grind)
    | exact superpose eq2074 eq56
    | exact resolve eq56 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2090 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq396 X0 y y
       have i₂ := eq2074
       grind)
    | exact superpose eq2074 eq396
    | exact resolve eq396 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074
  have eq2093 : y = (k y y) := by grind
  clear eq2078
  have eq2100 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq209 eq2085
    | exact resolve eq2085 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq2085
  have eq2108 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2100
    | exact resolve eq2100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100
  have eq2118 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq81
       have i₂ := eq2093
       grind)
    | exact superpose eq2093 eq81
    | exact resolve eq81 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq2093
  have eq2122 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2118
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2118
    | exact resolve eq2118 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2118
  have eq2199 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2122 eq74
    | (have j0 := eq74 x (σ y)
       grind)
    | exact resolve eq74 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq2122
  have eq2200 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq2199
  have eq2265 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2200 eq57
    | exact resolve eq57 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq2200
  have eq2281 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq224 eq2265
    | exact resolve eq2265 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265
  have eq2290 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq26 eq2281
    | exact resolve eq2281 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2281
  have eq2350 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2290 eq1653
    | exact resolve eq1653 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq3337 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq2290 eq2090
    | exact resolve eq2090 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3986 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) (M.op x y)) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (σ x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq224 eq232
    | (have j0 := eq232 X0 X1
       grind)
    | exact resolve eq232 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq3987 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (σ x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq2290 eq3986
    | (have j0 := eq3986 X0 X1
       grind)
    | exact resolve eq3986 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3986
  have eq3988 : ∀ X0 X1 : G, (M.op (σ x) (M.op x y)) = (k (σ x) (M.op X0 X1)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq224 eq3987
    | exact resolve eq3987 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq3987
  have eq3989 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq2290 eq3988
    | exact resolve eq3988 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3988
  have eq5179 : ∀ X0 X4 X5 : G, (k X0 (M.op X4 X5)) = (M.op X0 y) ∨ (M.op X0 (M.op x y)) ≠ X0 := by
    intro X0 X4 X5
    first
    | exact superpose eq2090 eq1263
    | (have j0 := eq1263 X0 X4 X5
       grind)
    | exact resolve eq1263 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq5180 : ∀ X0 X4 X5 : G, (M.op X0 y) ≠ X0 ∨ (k X0 (M.op X4 X5)) = (M.op X0 y) := by
    intro X0 X4 X5
    first
    | exact superpose eq2090 eq5179
    | (have j0 := eq5179 X0 X4 X5
       grind)
    | exact resolve eq5179 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5179
  have eq5392 : ∀ X0 X3 : G, (M.op X3 y) = X3 ∨ (M.op X3 X3) = (k X3 (M.op X0 (M.op x y))) := by
    intro X0 X3
    first
    | exact superpose eq2090 eq1848
    | (have j0 := eq1848 X0 X3
       grind)
    | exact resolve eq1848 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848
  have eq5393 : ∀ X0 X3 : G, (M.op X3 X3) = (k X3 (M.op X0 y)) ∨ (M.op X3 y) = X3 := by
    intro X0 X3
    first
    | exact superpose eq2090 eq5392
    | (have j0 := eq5392 X0 X3
       grind)
    | exact resolve eq5392 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5392
  have eq5660 : ∀ X0 X1 : G, (k X0 (M.op X1 y)) ≠ X0 ∨ (k X0 X0) = (k X0 (M.op X1 y)) ∨ (M.op X0 y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 x x
       have i₂ := eq5393 X0 x
       grind)
    | exact superpose eq5393 eq13
    | (have j1 := eq5393 X0 X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq5393 X0 x
       grind)
    | exact resolve eq13 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5693 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op x y)) = (k (M.op X0 X1) (M.op X2 y)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq396 (M.op X0 X1) X0 X1
       have i₂ := eq5393 X2 (M.op X0 X1)
       grind)
    | exact superpose eq5393 eq396
    | (have j1 := eq5393 X0 (M.op X0 X1)
       grind)
    | exact resolve eq396 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq5698 : ∀ X0 X1 : G, (σ (k X0 X0)) = (k (σ X0) (M.op X1 y)) ∨ (σ X0) = (k (σ X0) (M.op X1 y)) ∨ (σ X0) = (M.op (σ X0) y) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X0
       have i₂ := eq5393 X0 (σ X0)
       grind)
    | exact superpose eq5393 eq88
    | (have j1 := eq5393 X0 (σ X0)
       grind)
    | exact resolve eq88 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5393
  have eq5725 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (k (M.op X0 X1) (M.op X2 y)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq2090 eq5693
    | (have j0 := eq5693 X0 X1 X2
       grind)
    | exact resolve eq5693 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5693
  have eq5777 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (k (M.op X0 X1) (M.op X2 y)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq5725 X0 X1 X2
       have j1 := eq5180 (M.op X0 X1) X2 y
       grind)
    | (have r₁ := eq5725 X0 X1 X2
       have r₂ := eq5180 (M.op X0 X1) x x
       grind)
    | exact resolve eq5725 eq5180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5180 eq5725
  have eq6674 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op X0 (M.op x y)) X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq334 X0 x X2 X3
       have i₂ := eq906 X0 x
       grind)
    | exact superpose eq906 eq334
    | exact resolve eq334 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq6675 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op X0 y) X2) := by
    intro X0 X2 X3
    first
    | exact superpose eq2090 eq6674
    | exact resolve eq6674 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6674
  have eq6676 : ∀ X0 X2 : G, (M.op (M.op X0 X2) (M.op x y)) = (M.op (M.op X0 y) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq6675 X0 X2 x
       have i₂ := eq906 (M.op X0 X2) x
       grind)
    | exact superpose eq906 eq6675
    | exact resolve eq6675 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6675
  have eq6677 : ∀ X0 X2 : G, (M.op (M.op X0 y) X2) = (M.op (M.op X0 X2) y) := by
    intro X0 X2
    first
    | exact superpose eq2090 eq6676
    | exact resolve eq6676 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6676
  have eq6830 : ∀ X0 : G, (M.op (M.op (σ x) (M.op x y)) y) = (M.op (M.op (M.op (σ x) X0) y) X0) := by
    intro X0
    first
    | exact superpose eq380 eq6677
    | exact resolve eq6677 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6677
  have eq6996 : ∀ X0 : G, (M.op (M.op (σ x) y) (M.op x y)) = (M.op (M.op (M.op (σ x) X0) y) X0) := by
    intro X0
    first
    | exact superpose eq985 eq6830
    | exact resolve eq6830 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985 eq6830
  have eq7053 : ∀ X0 : G, (M.op (M.op (σ x) y) y) = (M.op (M.op (M.op (σ x) X0) y) X0) := by
    intro X0
    first
    | exact superpose eq2090 eq6996
    | exact resolve eq6996 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6996
  have eq7097 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op (M.op (M.op (σ x) X0) y) X0) := by
    intro X0
    first
    | exact superpose eq380 eq7053
    | exact resolve eq7053 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7053
  have eq7127 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) y) X0) := by
    intro X0
    first
    | exact superpose eq2290 eq7097
    | exact resolve eq7097 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7097
  have eq13394 : (σ (M.op (σ x) (σ y))) ≠ (σ (M.op (σ x) (σ y))) ∨ (σ (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2350 eq1411
    | (have j0 := eq1411 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1411 eq2350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13398 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1411 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq1411
    | (have j0 := eq1411 (τ X0)
       grind)
    | exact resolve eq1411 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13402 : (σ (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) := by grind
  clear eq13394
  have eq13420 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13398 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq13398
    | (have j0 := eq13398 X0
       grind)
    | exact resolve eq13398 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13398
  have eq13431 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13420 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq13420
    | (have j0 := eq13420 X0
       grind)
    | exact resolve eq13420 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13420
  have eq17216 : (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq13402 eq906
    | exact resolve eq906 eq13402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17247 : (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq2090 eq17216
    | exact resolve eq17216 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17216
  have eq17266 : (σ (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq13402 eq17247
    | exact resolve eq17247 eq13402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13402 eq17247
  have eq22020 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ X1)) = (M.op (σ X0) y) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | exact superpose eq2090 eq1421
    | (have j0 := eq1421 X0 X1
       grind)
    | exact resolve eq1421 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421
  have eq22373 : ∀ X0 X1 : G, (σ (k (k X0 X1) X1)) = (M.op (σ X0) y) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (k X0 X1) X1
       have i₂ := eq22020 X0 X1
       grind)
    | exact superpose eq22020 eq88
    | (have j0 := eq88 X0 X1
       have j1 := eq22020 X0 X1
       grind)
    | exact resolve eq88 eq22020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq22020
  have eq22424 : ∀ X0 X1 : G, (σ (k (k X0 X1) X1)) = (M.op (σ X0) y) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq22373 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22373
  have eq32363 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 y) X1) ∨ (M.op X2 (M.op x y)) = X2 ∨ (k X2 (M.op X0 X1)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq2090 eq1836
    | (have j0 := eq1836 X0 X1 X2
       grind)
    | exact resolve eq1836 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq32364 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 y) X1) ∨ (M.op X2 y) = X2 ∨ (k X2 (M.op X0 X1)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq2090 eq32363
    | (have j0 := eq32363 X0 X1 X2
       grind)
    | exact resolve eq32363 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090 eq32363
  have eq32377 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op x y)) X0) ≠ (M.op (M.op (σ x) y) X0) ∨ (M.op X1 y) = X1 ∨ (M.op X1 X1) = (k X1 (M.op (M.op (σ x) y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq380 eq32364
    | (have j0 := eq32364 (M.op (σ x) y) X0 X1
       grind)
    | exact resolve eq32364 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq32364
  have eq32512 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (M.op x y)) X0) ∨ (M.op X1 y) = X1 ∨ (M.op X1 X1) = (k X1 (M.op (M.op (σ x) y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq3337 eq32377
    | (have j0 := eq32377 X0 X1
       grind)
    | exact resolve eq32377 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32377
  have eq32555 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op X1 y) = X1 ∨ (M.op X1 X1) = (k X1 (M.op (M.op (σ x) y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq2290 eq32512
    | (have j0 := eq32512 X0 X1
       grind)
    | exact resolve eq32512 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290 eq32512
  have eq32556 : ∀ X0 X1 : G, (M.op X1 y) = X1 ∨ (M.op X1 X1) = (k X1 (M.op (M.op (σ x) y) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32555 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32555
  have eq32586 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | exact superpose eq3337 eq32556
    | (have j0 := eq32556 X0 X1
       grind)
    | exact resolve eq32556 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32556
  have eq39400 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (k (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq7127 eq5777
    | exact resolve eq5777 eq7127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7127
  have eq94612 : ∀ X0 : G, (M.op (σ x) y) = (σ (k (τ (k (σ x) X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq22424 x (τ X0)
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq22424
    | (have j0 := eq22424 X0 (τ X0)
       grind)
    | exact resolve eq22424 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq95092 : ∀ X0 : G, (M.op (σ x) y) = (k (k (σ x) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq94612 X0
       have i₂ := eq34 (k sF2 X0) (τ X0)
       grind)
    | exact superpose eq34 eq94612
    | (have j0 := eq94612 X0
       grind)
    | exact resolve eq94612 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94612
  have eq95319 : ∀ X0 : G, (M.op (σ x) y) = (k (k (σ x) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq95092 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq95092
    | (have j0 := eq95092 X0
       grind)
    | exact resolve eq95092 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95092
  have eq95452 : ∀ X0 : G, (M.op (σ x) y) = (k (k (σ x) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq95319 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq95319
    | (have j0 := eq95319 X0
       grind)
    | exact resolve eq95319 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95319
  have eq95509 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (k (σ x) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq3337 eq95452
    | (have j0 := eq95452 X0
       grind)
    | exact resolve eq95452 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95452
  have eq95538 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (k (σ x) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq95509 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq95509
    | (have j0 := eq95509 X0
       grind)
    | exact resolve eq95509 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95509
  have eq220295 : ∀ X0 : G, (σ (k x x)) = (k (σ x) (M.op X0 y)) ∨ (σ x) = (k (σ x) (M.op X0 y)) ∨ (σ x) = (M.op (σ x) y) := by
    intro X0
    first
    | (have i₁ := eq5698 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5698
    | (have j0 := eq5698 x X0
       grind)
    | exact resolve eq5698 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5698
  have eq220714 : ∀ X0 : G, (k (σ x) (σ x)) = (k (σ x) (M.op X0 y)) ∨ (σ x) = (k (σ x) (M.op X0 y)) ∨ (σ x) = (M.op (σ x) y) := by
    intro X0
    first
    | (have i₁ := eq220295 X0
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq220295
    | (have j0 := eq220295 X0
       grind)
    | exact resolve eq220295 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq220295
  have eq220773 : ∀ X0 : G, (k (σ x) (σ x)) = (k (σ x) (M.op X0 y)) ∨ (σ x) = (M.op (σ x) y) := by
    intro X0
    first
    | (have j0 := eq220714 X0
       have j1 := eq5660 (σ x) X0
       grind)
    | (have r₁ := eq220714 x
       have r₂ := eq5660 (σ x) x
       grind)
    | exact resolve eq220714 eq5660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5660 eq220714
  have eq220812 : ∀ X0 : G, (k (σ x) (σ x)) = (k (σ x) (M.op X0 y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3337 eq220773
    | (have j0 := eq220773 X0
       grind)
    | exact resolve eq220773 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220773
  have eq636719 : ∀ X0 X1 : G, (M.op (σ (τ X0)) y) = (σ (k (τ (k X0 X1)) (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22424 (τ X0) (τ X1)
       have i₂ := eq1758 X1 X0
       grind)
    | exact superpose eq1758 eq22424
    | (have j0 := eq22424 X0 (τ X1)
       grind)
    | exact resolve eq22424 eq1758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758 eq22424
  have eq636788 : ∀ X0 X1 : G, (M.op (σ (τ X0)) y) = (k (k X0 X1) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq636719 X0 X1
       have i₂ := eq34 (k X0 X1) (τ X1)
       grind)
    | exact superpose eq34 eq636719
    | (have j0 := eq636719 X0 X1
       grind)
    | exact resolve eq636719 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq636719
  have eq636999 : ∀ X0 X1 : G, (k (k X0 X1) X1) = (M.op (σ (τ X0)) y) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq636788 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq636788
    | (have j0 := eq636788 X0 X1
       grind)
    | exact resolve eq636788 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636788
  have eq637195 : ∀ X0 X1 : G, (k (k X0 X1) X1) = (M.op X0 y) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq636999 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq636999
    | (have j0 := eq636999 X0 X1
       grind)
    | exact resolve eq636999 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636999
  have eq637331 : ∀ X0 X1 : G, (k (k X0 X1) X1) = (M.op X0 y) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq637195 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq637195
    | (have j0 := eq637195 X0 X1
       grind)
    | exact resolve eq637195 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637195
  have eq1350666 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq220812 eq32586
    | (have j0 := eq32586 x (σ x)
       grind)
    | exact resolve eq32586 eq220812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32586 eq220812
  have eq1350770 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3337 eq1350666
    | exact resolve eq1350666 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350666
  have eq1350771 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1350770
  have eq1353706 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1350771 eq49
    | exact resolve eq49 eq1350771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1350771
  have eq2189461 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq136
       have i₂ := eq637331 x x
       grind)
    | exact superpose eq637331 eq136
    | (have j1 := eq637331 x x
       grind)
    | exact resolve eq136 eq637331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq637331
  have eq2189754 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2189461
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2189461
    | exact resolve eq2189461 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2189461
  have eq2191727 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq2189754
    | exact resolve eq2189754 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2189754
  have eq2215862 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2191727 eq95538
    | (have j0 := eq95538 (σ x)
       grind)
    | exact resolve eq95538 eq2191727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95538
  have eq2215979 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2215862
       have r₂ := eq27
       grind)
    | exact resolve eq2215862 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2215862
  have eq2216024 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2215979 eq1353706
    | exact resolve eq1353706 eq2215979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353706 eq2215979
  have eq2216207 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq2216024
    | exact resolve eq2216024 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2216024
  have eq2216232 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13431 x
       grind)
    | (have r₁ := eq2216207
       have r₂ := eq13431 x
       grind)
    | exact resolve eq2216207 eq13431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13431 eq2216207
  have eq2216256 : x ≠ x ∨ x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq2216232
       grind)
    | exact superpose eq2216232 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq2216232
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2216232
       grind)
    | exact resolve eq13 eq2216232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2216320 : (M.op x y) = (k x (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39400 x x
       have i₂ := eq2216232
       grind)
    | exact superpose eq2216232 eq39400
    | exact resolve eq39400 eq2216232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39400 eq2216232
  have eq2216348 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2216256
  have eq2216357 : (M.op x y) = (k x (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2216320
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2216320
    | exact resolve eq2216320 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2216320
  have eq2216562 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1411 x
       have i₂ := eq2216348
       grind)
    | exact superpose eq2216348 eq1411
    | (have j0 := eq1411 x
       grind)
    | exact resolve eq1411 eq2216348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411 eq2216348
  have eq2216671 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2216562
  have eq2216749 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2216671
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2216671
    | exact resolve eq2216671 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216671
  have eq2221259 : ∀ X0 : G, (M.op (σ x) y) = (k (σ x) (M.op X0 y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2216749 eq5777
    | exact resolve eq5777 eq2216749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5777 eq2216749
  have eq2221392 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op X0 y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3337 eq2221259
    | exact resolve eq2221259 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3337 eq2221259
  have eq2221438 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op X0 y)) := by
    intro X0
    first
    | (have j0 := eq2221392 X0
       have j1 := eq3989 X0 y
       grind)
    | (have r₁ := eq2221392 X0
       have r₂ := eq3989 X0 x
       grind)
    | exact resolve eq2221392 eq3989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3989 eq2221392
  have eq2230210 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq17266 eq2221438
    | exact resolve eq2221438 eq17266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17266 eq2221438
  have eq2230501 : (M.op (σ x) (σ y)) = (σ (k x (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq35 eq2230210
    | exact resolve eq2230210 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq2230210
  have eq2232703 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2216357 eq2230501
    | exact resolve eq2230501 eq2216357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216357 eq2230501
  have eq2233283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2232703
    | exact resolve eq2232703 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232703
  have eq2233384 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2233283
       have r₂ := eq27
       grind)
    | exact resolve eq2233283 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2233283
  have eq2234879 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq2233384 eq27
    | exact resolve eq27 eq2233384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2234892 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2233384 eq2350
    | exact resolve eq2350 eq2233384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350 eq2233384
  have eq2237255 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2234892 eq2191727
    | exact resolve eq2191727 eq2234892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2191727
  have eq2237452 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2234892 eq2237255
    | exact resolve eq2237255 eq2234892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2234892 eq2237255
  have eq2237493 : x = (M.op x x) := by
    first
    | (have r₁ := eq2237452
       have r₂ := eq2234879
       grind)
    | exact resolve eq2237452 eq2234879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237452
  have eq2242210 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq906 x x
       have i₂ := eq2237493
       grind)
    | exact superpose eq2237493 eq906
    | exact resolve eq906 eq2237493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq2242336 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2108 eq2242210
    | exact resolve eq2242210 eq2108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2108 eq2242210
  have eq2242381 : x = (M.op x y) := by
    first
    | (have i₁ := eq2242336
       have i₂ := eq2237493
       grind)
    | exact superpose eq2237493 eq2242336
    | exact resolve eq2242336 eq2237493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237493 eq2242336
  have eq2242446 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2242381 eq20
    | exact resolve eq20 eq2242381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2242381
  have eq2243918 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2242446
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2242446
    | exact resolve eq2242446 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2242446
  have eq2244036 : False := by grind
  exact eq2244036

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxx_pyx_Equation4521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
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
  clear eq24
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
  have eq58 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X3 X4 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) X2) X2) ∨ (k X3 (M.op X0 X1)) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq76
    | (have j1 := eq79 y x
       grind)
    | exact resolve eq76 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq373 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 x y X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 X0 X1 X2 x y
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq883 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq373 X0 x x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq373
    | (have j1 := eq14 X0 x y X1
       grind)
    | exact resolve eq373 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1427 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op x y)) ∨ (k X3 (M.op X0 X1)) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq69 X0 X1 x X3
       have i₂ := eq883 (M.op X0 X1) x
       grind)
    | exact superpose eq883 eq69
    | (have j0 := eq69 X0 X1 x X3
       grind)
    | exact resolve eq69 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq1658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq113 eq79
    | (have j0 := eq79 (σ y) (σ x)
       grind)
    | exact resolve eq79 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1658
    | exact resolve eq1658 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658
  have eq1662 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1659
       have r₂ := eq27
       grind)
    | exact resolve eq1659 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659
  have eq1694 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1662 eq373
    | exact resolve eq373 eq1662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1752 : (σ x) = (M.op (σ y) (M.op x y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1694 eq1662
    | exact resolve eq1662 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662 eq1694
  have eq1753 : (σ x) = (M.op (σ y) (M.op x y)) ∨ x = (M.op y x) := by grind
  clear eq1752
  have eq1814 : (σ x) = (M.op (σ x) (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1753 eq883
    | exact resolve eq883 eq1753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq1848 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (M.op x y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1814 eq1427
    | exact resolve eq1427 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq1849 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1848 X0
       grind)
    | (have r₁ := eq1848 X0
       have r₂ := eq1814
       grind)
    | exact resolve eq1848 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814 eq1848
  have eq2080 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1849 eq113
    | exact resolve eq113 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq1849
  have eq2084 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq2080
  have eq2088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq2084
    | exact resolve eq2084 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084
  have eq2090 : x = (M.op y x) := by
    first
    | (have r₁ := eq2088
       have r₂ := eq27
       grind)
    | exact resolve eq2088 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq2103 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq373 X0 y x
       have i₂ := eq2090
       grind)
    | exact superpose eq2090 eq373
    | exact resolve eq373 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq2104 : (M.op x x) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq883 y x
       have i₂ := eq2090
       grind)
    | exact superpose eq2090 eq883
    | exact resolve eq883 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq2230 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq2103 eq2104
    | exact resolve eq2104 eq2103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103 eq2104
  have eq2231 : x = (M.op x x) := by
    first
    | (have i₁ := eq2230
       have i₂ := eq2090
       grind)
    | exact superpose eq2090 eq2230
    | exact resolve eq2230 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090 eq2230
  have eq2233 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq2231
       grind)
    | exact superpose eq2231 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq2231
       grind)
    | exact resolve eq13 eq2231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2248 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq2233 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2233
  have eq2282 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2248 x
       grind)
    | exact superpose eq2248 eq43
    | exact resolve eq43 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq2283 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq2248 y
       grind)
    | exact superpose eq2248 eq76
    | exact resolve eq76 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq2248
  have eq2289 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2283
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2283
    | exact resolve eq2283 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2283
  have eq2290 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2282
       have i₂ := eq2231
       grind)
    | exact superpose eq2231 eq2282
    | exact resolve eq2282 eq2231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231 eq2282
  have eq2292 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq2289
    | exact resolve eq2289 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2289
  have eq2293 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2290
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2290
    | exact resolve eq2290 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2290
  have eq2311 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2293 eq79
    | (have j0 := eq79 (σ x) (σ x)
       grind)
    | exact resolve eq79 eq2293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq2293
  have eq2312 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2311
  have eq2384 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq2312 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq2312
       grind)
    | exact resolve eq13 eq2312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312
  have eq2400 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq2384 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384
  have eq2746 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2400 eq2292
    | exact resolve eq2292 eq2400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2292 eq2400
  have eq2753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2746
    | exact resolve eq2746 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2746
  have eq2761 : False := by grind
  exact eq2761

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation4521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
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
  have eq52 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X4) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 X0 x x X4
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X1) (M.op X4 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X0 X2 X3 (M.op X4 X5)
       have i₂ := eq14 X0 X4 X5 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X3) (M.op X4 X5)) = (M.op (M.op X0 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 (M.op X0 X3) X4 X5 X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 X1 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) X2) X2) ∨ (k X3 (M.op X0 X1)) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X2 X3) ∨ (M.op X0 X0) = X0 ∨ (M.op X2 X3) = (k (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X2 X3) X0
       have i₂ := eq14 X0 X2 X3 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X2 X3) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X3) X3) X0
       have r₂ := eq14 X0 (M.op X0 X3) X3 X3
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X0 (M.op X1 X2)))
       have r₂ := eq14 X0 X1 X2 (M.op X0 (M.op X1 X2))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq98
    | (have j0 := eq98 (σ X0) (σ X1)
       grind)
    | exact resolve eq98 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq98 y x
       grind)
    | exact superpose eq98 eq76
    | (have j1 := eq98 y x
       grind)
    | exact resolve eq76 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq123
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq123
    | exact resolve eq123 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq124 eq98
    | (have j0 := eq98 (σ y) (σ x)
       grind)
    | exact resolve eq98 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq128
       have r₂ := eq27
       grind)
    | exact resolve eq128 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq133 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq131
    | exact resolve eq131 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq135 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133 eq27
    | exact resolve eq27 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq144 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  clear eq37
  have eq154 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq143 eq16
    | exact resolve eq16 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133 eq82
    | (have r₁ := eq82
       have r₂ := eq133
       grind)
    | exact resolve eq82 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq133
  have eq746 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq745
  have eq749 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq746 eq124
    | exact resolve eq124 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq753 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq749
  have eq758 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq753
       have r₂ := eq135
       grind)
    | exact resolve eq753 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq753
  have eq770 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq758 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq758
       grind)
    | exact resolve eq13 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq771 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq770 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq771 eq124
    | exact resolve eq124 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq771
  have eq963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq960
  have eq968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq963
    | exact resolve eq963 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq970 : y = (M.op x y) := by
    first
    | (have r₁ := eq968
       have r₂ := eq27
       grind)
    | exact resolve eq968 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq972 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq970 eq20
    | exact resolve eq20 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq970 eq226
    | exact resolve eq226 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq981 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq979
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq979
    | exact resolve eq979 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq987 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq972
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq972
    | exact resolve eq972 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq988 : y = (M.op y y) := by
    first
    | exact superpose eq970 eq981
    | exact resolve eq981 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq1043 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op X0 X1)) = (M.op (M.op (M.op x y) y) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 x y X0 X1 X2 X3
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 x y X0 X1 X2 X3
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1167 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq226 eq1043
    | exact resolve eq1043 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1173 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq970 eq1167
    | exact resolve eq1167 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1179 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1173 X0 X1 X2 X3
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1173
    | (have j0 := eq1173 X0 X1 X2 X3
       grind)
    | exact resolve eq1173 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1185 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op X0 X1)) = (M.op y (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq970 eq1179
    | exact resolve eq1179 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1190 : ∀ X2 X3 : G, (M.op (M.op x y) y) = (M.op y (M.op X2 X3)) := by
    intro X2 X3
    first
    | (have i₁ := eq1185 x x X2 X3
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq1185
    | exact resolve eq1185 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1194 : ∀ X2 X3 : G, (M.op x (M.op x y)) = (M.op y (M.op X2 X3)) := by
    intro X2 X3
    first
    | exact superpose eq226 eq1190
    | exact resolve eq1190 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1197 : ∀ X2 X3 : G, (M.op x y) = (M.op y (M.op X2 X3)) := by
    intro X2 X3
    first
    | exact superpose eq970 eq1194
    | exact resolve eq1194 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1200 : ∀ X2 X3 : G, (M.op x y) = (M.op y (M.op X2 X3)) := by
    intro X2 X3
    first
    | (have i₁ := eq1197 X2 X3
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1197
    | (have j0 := eq1197 X2 X3
       grind)
    | exact resolve eq1197 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1202 : ∀ X2 X3 : G, y = (M.op y (M.op X2 X3)) := by
    intro X2 X3
    first
    | exact superpose eq970 eq1200
    | exact resolve eq1200 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1204 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq987 eq26
    | exact resolve eq26 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1382 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) (M.op X1 X2)) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 x x x X0 X1 X2
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq1465 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (M.op x X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq226 eq1382
    | exact resolve eq1382 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq1474 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) (M.op X1 X2)) = (M.op (M.op x y) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq970 eq1465
    | exact resolve eq1465 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1478 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (M.op (M.op x X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1474 X0 X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1474
    | (have j0 := eq1474 X0 X1 X2
       grind)
    | exact resolve eq1474 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq1482 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) (M.op X1 X2)) = (M.op y X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq970 eq1478
    | exact resolve eq1478 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478
  have eq1547 : ∀ X0 : G, y = (M.op (M.op y X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1202 x x
       have i₂ := eq14 y x x X0
       grind)
    | exact superpose eq14 eq1202
    | exact resolve eq1202 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1718 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq102
    | (have j0 := eq102 (M.op x y) X0
       grind)
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq102
  have eq1745 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq970 eq1718
    | (have j0 := eq1718 X0
       grind)
    | exact resolve eq1718 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq1831 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op (M.op (M.op x y) X0) X0) ∨ (k X1 (M.op x y)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq69
    | (have j0 := eq69 x y X0 X1
       grind)
    | exact resolve eq69 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq1886 : ∀ X0 X1 : G, y ≠ (M.op (M.op y X0) X0) ∨ (k X1 (M.op x y)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq970 eq1831
    | (have j0 := eq1831 X0 X1
       grind)
    | exact resolve eq1831 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq1888 : ∀ X1 : G, (k X1 (M.op x y)) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | (have j0 := eq1886 x X1
       grind)
    | (have r₁ := eq1886 x X1
       have r₂ := eq1547 x
       grind)
    | exact resolve eq1886 eq1547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547 eq1886
  have eq1889 : ∀ X1 : G, (M.op y X1) = (k X1 y) := by
    intro X1
    first
    | exact superpose eq970 eq1888
    | exact resolve eq1888 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq1891 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq1889 y
       grind)
    | exact superpose eq1889 eq77
    | exact resolve eq77 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1889
  have eq1896 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1891
       have i₂ := eq988
       grind)
    | exact superpose eq988 eq1891
    | exact resolve eq1891 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988 eq1891
  have eq1900 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq987 eq1896
    | exact resolve eq1896 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896
  have eq1902 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1900
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1900
    | exact resolve eq1900 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900
  have eq1904 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq987 eq1902
    | exact resolve eq1902 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902
  have eq1940 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ (M.op X0 X1) = (k (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq79 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79
    | (have j0 := eq79 x y X0 X1
       grind)
    | exact resolve eq79 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2001 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (M.op X0 X1) = (k (M.op X0 X1) x) := by
    intro X0 X1
    first
    | exact superpose eq226 eq1940
    | (have j0 := eq1940 X0 X1
       grind)
    | (have r₁ := eq1940 x (M.op x y)
       have r₂ := eq226
       grind)
    | exact resolve eq1940 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq1940
  have eq2007 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op X0 X1) ∨ x = (M.op x x) ∨ (M.op X0 X1) = (k (M.op X0 X1) x) := by
    intro X0 X1
    first
    | exact superpose eq970 eq2001
    | (have j0 := eq2001 X0 X1
       grind)
    | exact resolve eq2001 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001
  have eq2011 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op X0 X1) ∨ x = (M.op x x) ∨ (M.op X0 X1) = (k (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq2007 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2007
    | (have j0 := eq2007 X0 X1
       grind)
    | (have r₁ := eq2007 x y
       have r₂ := eq18
       grind)
    | exact resolve eq2007 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2007
  have eq2015 : ∀ X0 X1 : G, y ≠ (M.op X0 X1) ∨ x = (M.op x x) ∨ (M.op X0 X1) = (k (M.op X0 X1) x) := by
    intro X0 X1
    first
    | exact superpose eq970 eq2011
    | (have j0 := eq2011 X0 X1
       grind)
    | exact resolve eq2011 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq2824 : ∀ X0 X1 X2 : G, (M.op (M.op x X2) X2) = (M.op y (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 x (M.op X0 X1) X2
       have i₂ := eq1482 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq1482 eq52
    | exact resolve eq52 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1482
  have eq2873 : ∀ X2 : G, y = (M.op (M.op x X2) X2) := by
    intro X2
    first
    | (have i₁ := eq2824 x x X2
       have i₂ := eq1202 x x
       grind)
    | exact superpose eq1202 eq2824
    | exact resolve eq2824 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824
  have eq4656 : (σ (k y x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1745 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1745
    | (have j0 := eq1745 x
       grind)
    | exact resolve eq1745 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1745
  have eq4706 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1204 eq4656
    | exact resolve eq4656 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4656
  have eq4720 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4706
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq4706
    | exact resolve eq4706 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq4706
  have eq4733 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq987 eq4720
    | exact resolve eq4720 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4720
  have eq4743 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1204 eq4733
    | exact resolve eq4733 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204 eq4733
  have eq4750 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq4743
       have r₂ := eq27
       grind)
    | exact resolve eq4743 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4743
  have eq4768 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq4750 eq154
    | exact resolve eq154 eq4750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq4771 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq970 eq4768
    | exact resolve eq4768 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq4768
  have eq5663 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq2015 y (M.op x x)
       have i₂ := eq1202 x x
       grind)
    | exact superpose eq1202 eq2015
    | (have r₁ := eq2015 y (M.op x x)
       have r₂ := eq1202 x x
       grind)
    | exact resolve eq2015 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202 eq2015
  have eq5690 : x = (M.op x x) ∨ y = (k y x) := by grind
  clear eq5663
  have eq5700 : x = (M.op x x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5690
       have i₂ := eq4771
       grind)
    | exact superpose eq4771 eq5690
    | exact resolve eq5690 eq4771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4771 eq5690
  have eq7254 : y = (M.op x x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2873 x
       have i₂ := eq5700
       grind)
    | exact superpose eq5700 eq2873
    | exact resolve eq2873 eq5700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2873
  have eq8615 : x = y ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5700
       have i₂ := eq7254
       grind)
    | exact superpose eq7254 eq5700
    | exact resolve eq5700 eq7254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5700 eq7254
  have eq8655 : y = (τ (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq8615
  have eq8707 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq8655 eq15
    | exact resolve eq15 eq8655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8655
  have eq8708 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq8707
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8707
    | exact resolve eq8707 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8707
  have eq8714 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq987 eq8708
    | exact resolve eq8708 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8708
  have eq8720 : x = y := by
    first
    | (have r₁ := eq8714
       have r₂ := eq27
       grind)
    | exact resolve eq8714 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8714
  have eq8733 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq144
       have i₂ := eq8720
       grind)
    | exact superpose eq8720 eq144
    | exact resolve eq144 eq8720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq8720
  have eq8763 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq987 eq8733
    | exact resolve eq8733 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987 eq8733
  have eq8774 : (σ (M.op x y)) = (σ (k (M.op x y) x)) := by
    first
    | exact superpose eq1904 eq8763
    | exact resolve eq8763 eq1904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904 eq8763
  have eq8784 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq143 eq8774
    | exact resolve eq8774 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq8774
  have eq8792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4750 eq8784
    | exact resolve eq8784 eq4750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4750 eq8784
  have eq8795 : False := by grind
  exact eq8795

/-- `Equation4533`: `x ◇ (y ◇ z) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_x_pyx_pxy_Equation4533 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4533 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4533.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X2) := by
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq177 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X0 (M.op X1 X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq16 X3 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq16 (M.op (M.op X0 X1) X1) X0 X1
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq188 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq179 eq188
    | exact resolve eq188 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq562 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
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
  have eq568 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq575 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq575 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq1187 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq576 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq576
    | (have j0 := eq576 (σ X0)
       grind)
    | exact resolve eq576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1832 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op X0 X1) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x (M.op X0 X1) X1
       have i₂ := eq185 X0 X1 x
       grind)
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2320 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op (M.op X0 X1) X1)
       have i₂ := eq1832 X0 X1
       grind)
    | exact superpose eq1832 eq13
    | (have j0 := eq13 X1 (M.op (M.op X0 X1) X1)
       grind)
    | (have r₁ := eq13 X1 (M.op (M.op X0 X1) X1)
       have r₂ := eq1832 X0 X1
       grind)
    | exact resolve eq13 eq1832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832
  have eq2382 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2320 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320
  have eq2461 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2382 x (M.op X0 X1)
       have i₂ := eq16 (M.op x (M.op X0 X1)) X0 X1
       grind)
    | exact superpose eq16 eq2382
    | exact resolve eq2382 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2472 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq193 eq2382
    | exact resolve eq2382 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq2496 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op (M.op X0 (σ y)) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq107 (M.op (M.op X0 sF3) sF3)
       have i₂ := eq2382 X0 sF3
       grind)
    | exact superpose eq2382 eq107
    | exact resolve eq107 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq2382
  have eq2497 : ∀ X0 : G, y = (k y (τ (M.op (M.op X0 (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq31 eq2496
    | exact resolve eq2496 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2496
  have eq3877 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq562
       grind)
    | exact superpose eq562 eq40
    | exact resolve eq40 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq562
  have eq3878 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3877
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3877
    | exact resolve eq3877 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3877
  have eq3880 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq3878
    | exact resolve eq3878 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3878
  have eq26534 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq2472 eq1187
    | (have j0 := eq1187 (M.op (M.op x y) y)
       grind)
    | exact resolve eq1187 eq2472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187 eq2472
  have eq26572 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq26534
  have eq27361 : ∀ X0 X1 : G, (M.op X0 (σ (M.op (M.op x y) y))) = (M.op X1 (σ (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq26572 eq181
    | exact resolve eq181 eq26572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27523 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (M.op X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq27361 eq26572
    | exact resolve eq26572 eq27361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26572 eq27361
  have eq27564 : ∀ X0 X1 : G, (σ (M.op X0 (M.op x y))) = (M.op X1 (σ (M.op X0 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq179 eq27523
    | exact resolve eq27523 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27523
  have eq29813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3880 eq568
    | exact resolve eq568 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq3880
  have eq29822 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq29813
       have r₂ := eq27
       grind)
    | exact resolve eq29813 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29813
  have eq29830 : y = (k y (τ (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29822 eq2497
    | exact resolve eq2497 eq29822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2497
  have eq29867 : y = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29822 eq29830
    | exact resolve eq29830 eq29822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29822 eq29830
  have eq29869 : y = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq29867
    | exact resolve eq29867 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29867
  have eq29870 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq29869
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq29869
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq29869
       have r₂ := eq13 x y
       grind)
    | exact resolve eq29869 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29869
  have eq29897 : (σ y) = (k (σ y) (M.op (σ y) (σ x))) ∨ y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29870 eq2461
    | exact resolve eq2461 eq29870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2461
  have eq29906 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29870 eq29897
    | exact resolve eq29897 eq29870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29870 eq29897
  have eq36119 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29906 eq152
    | exact resolve eq152 eq29906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq29906
  have eq36128 : y = (k y y) ∨ y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq36119
    | exact resolve eq36119 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq36119
  have eq36129 : y = (k y y) ∨ y = (M.op y x) := by grind
  clear eq36128
  have eq36142 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq576 y
       have i₂ := eq36129
       grind)
    | exact superpose eq36129 eq576
    | (have j0 := eq576 y
       grind)
    | (have r₁ := eq576 y
       have r₂ := eq36129
       grind)
    | exact resolve eq576 eq36129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq36129
  have eq36145 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq36142
  have eq36177 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 y y x
       have i₂ := eq36145
       grind)
    | exact superpose eq36145 eq181
    | exact resolve eq181 eq36145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq36540 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq36177 x X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq36177 X0 x
       grind)
    | exact superpose eq36177 eq18
    | (have j1 := eq36177 x X0
       grind)
    | exact resolve eq18 eq36177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36177
  have eq36717 : y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq36145
       have i₂ := eq36540 y
       grind)
    | exact superpose eq36540 eq36145
    | exact resolve eq36145 eq36540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36145 eq36540
  have eq36743 : y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq36717
  have eq36806 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq185 y x x
       have i₂ := eq36743
       grind)
    | exact superpose eq36743 eq185
    | exact resolve eq185 eq36743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq36842 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36743 eq36806
    | exact resolve eq36806 eq36743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36743 eq36806
  have eq36976 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq36842 x
       grind)
    | exact superpose eq36842 eq18
    | (have j1 := eq36842 x
       grind)
    | exact resolve eq18 eq36842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36842
  have eq36999 : y = (M.op x y) := by grind
  clear eq36976
  have eq37017 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq36999
       grind)
    | exact superpose eq36999 eq18
    | exact resolve eq18 eq36999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq37018 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq36999
       grind)
    | exact superpose eq36999 eq24
    | exact resolve eq24 eq36999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq37109 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq179 eq37017
    | exact resolve eq37017 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq37017
  have eq37111 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq37109
       have i₂ := eq36999
       grind)
    | exact superpose eq36999 eq37109
    | exact resolve eq37109 eq36999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36999 eq37109
  have eq37113 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq37018 eq20
    | exact resolve eq20 eq37018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37018
  have eq37588 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq37111 eq27564
    | exact resolve eq27564 eq37111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27564 eq37111
  have eq37628 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq37588
    | (have j0 := eq37588 X0
       grind)
    | exact resolve eq37588 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq37588
  have eq37641 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq37113 eq37628
    | exact resolve eq37628 eq37113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37628
  have eq37923 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37641 eq26
    | (have j1 := eq37641 (σ x)
       grind)
    | exact resolve eq26 eq37641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq37641
  have eq38014 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq37923 eq27
    | exact resolve eq27 eq37923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq37923
  have eq38095 : False := by grind
  exact eq38095

/-- `Equation4542`: `x ◇ (y ◇ z) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pxx_pxy_Equation4542 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4542 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4542.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X0) X2) := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X3 X0)) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X3 X0)
       have i₂ := eq14 X1 X3 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X2 X0) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X1)) = (M.op (M.op (M.op X0 X1) X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X0) X3 X1
       have i₂ := eq14 X1 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X2 X0))) = (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X2 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X1 X2
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X2 X0) ∨ (k X2 (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X2 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X2 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X3 X0)) = (M.op (M.op X0 X2) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq56 X0 x X2 X3
       have i₂ := eq14 X2 (M.op X0 x) X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq79
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79
    | exact resolve eq79 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq86
    | exact resolve eq86 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq96 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq97 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq106 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq16
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq401 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq63
    | (have j0 := eq63 X0 X1 y x
       grind)
    | exact resolve eq63 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq63
    | (have j0 := eq63 X0 X1 (σ y) (σ x)
       grind)
    | exact resolve eq63 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 X2 : G, (M.op X2 (M.op x y)) = (M.op X2 (M.op X0 (M.op X1 y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq401 X2 (M.op y X0)
       have i₂ := eq14 X0 X1 y
       grind)
    | exact superpose eq14 eq401
    | exact resolve eq401 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq401 X0 x
       have i₂ := eq14 X0 x y
       grind)
    | exact superpose eq14 eq401
    | (have j1 := eq14 X0 x y
       grind)
    | exact resolve eq401 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X2 : G, (M.op X2 (M.op x y)) = (M.op X2 (M.op X0 (M.op x y))) := by
    intro X0 X2
    first
    | (have i₁ := eq443 X0 x X2
       have i₂ := eq401 X0 x
       grind)
    | (have i₁ := eq443 X0 x X2
       have i₂ := eq401 X0 x
       grind)
    | exact superpose eq401 eq443
    | (have j0 := eq443 X0 x X2
       grind)
    | exact resolve eq443 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq464 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op X2 (M.op X0 (M.op X1 (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq403 X0 (M.op sF3 X0)
       have i₂ := eq14 X0 X1 sF3
       grind)
    | exact superpose eq14 eq403
    | exact resolve eq403 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq403 X0 x
       have i₂ := eq14 X0 x sF3
       grind)
    | exact superpose eq14 eq403
    | (have j1 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq403 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X2 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op X2 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0 X2
    first
    | exact superpose eq403 eq464
    | (have j0 := eq464 X0 (σ x) X2
       grind)
    | exact resolve eq464 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq642 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op (M.op (M.op X1 y) X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X1 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59
    | (have j0 := eq59 X1 y X0 x
       grind)
    | exact resolve eq59 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ y)) X1) (σ y)) = (M.op (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq59
    | (have j0 := eq59 X1 (σ y) X0 (σ x)
       grind)
    | exact resolve eq59 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq921 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq67 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq67
    | (have j0 := eq67 y X0 x
       grind)
    | exact resolve eq67 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq67
    | (have j0 := eq67 (σ y) X0 (σ x)
       grind)
    | exact resolve eq67 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq974 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq467 eq923
    | exact resolve eq923 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq976 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq921 X0
       have i₂ := eq446 X0
       grind)
    | exact superpose eq446 eq921
    | exact resolve eq921 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq1291 : ∀ X0 : G, (M.op (σ y) X0) ≠ (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq66
    | (have j0 := eq66 X0 (σ x) (σ y)
       grind)
    | exact resolve eq66 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1934 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op X2 X0)) (M.op x y)) = (M.op X0 (M.op X1 (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq463 X2 (M.op sF0 (M.op X1 X2))
       have i₂ := eq60 sF0 X1 X2 x
       grind)
    | exact superpose eq60 eq463
    | exact resolve eq463 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq1936 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X2 X0)) (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq484 X2 (M.op sF4 (M.op X1 X2))
       have i₂ := eq60 sF4 X1 X2 x
       grind)
    | exact superpose eq60 eq484
    | exact resolve eq484 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq484
  have eq1957 : ∀ X0 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X2 X0)) (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | (have i₁ := eq1936 x X0 X2
       have i₂ := eq57 X0 x sF4 x
       grind)
    | exact superpose eq57 eq1936
    | exact resolve eq1936 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq1959 : ∀ X0 X2 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = (M.op (M.op (M.op x y) (M.op X2 X0)) (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq1934 x X0 X2
       have i₂ := eq57 X0 x sF0 x
       grind)
    | exact superpose eq57 eq1934
    | exact resolve eq1934 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1934
  have eq2038 : ∀ X0 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) = (M.op (M.op X2 X0) (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | exact superpose eq974 eq1957
    | exact resolve eq1957 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq2040 : ∀ X0 X2 : G, (M.op (M.op X2 X0) (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0 X2
    first
    | exact superpose eq976 eq1959
    | exact resolve eq1959 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq2090 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X2 X0) (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | exact superpose eq974 eq2038
    | exact resolve eq2038 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq2038
  have eq2091 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op (M.op X2 X0) (M.op x y)) := by
    intro X0 X2
    first
    | exact superpose eq976 eq2040
    | exact resolve eq2040 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976 eq2040
  have eq2629 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq2630 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2629 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2629
  have eq3845 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op (M.op X1 y) X1) y) := by
    intro X1
    first
    | exact superpose eq2091 eq642
    | exact resolve eq642 eq2091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq3882 : ∀ X0 : G, (M.op (M.op X0 y) X0) = (M.op (M.op X0 (M.op x y)) (M.op (M.op X0 y) X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0 y (M.op X0 y)
       have i₂ := eq3845 X0
       grind)
    | exact superpose eq3845 eq67
    | exact resolve eq67 eq3845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845
  have eq3931 : ∀ X0 : G, (M.op (M.op X0 y) X0) = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq3882 x
       have i₂ := eq59 sF0 x x (M.op x y)
       grind)
    | exact superpose eq59 eq3882
    | exact resolve eq3882 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3882
  have eq3973 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) X0) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq2091 eq3931
    | exact resolve eq3931 eq2091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091 eq3931
  have eq4021 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op X1 (σ y)) X1) (σ y)) := by
    intro X1
    first
    | exact superpose eq2090 eq644
    | exact resolve eq644 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq4058 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op X0 (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq4021 eq67
    | exact resolve eq67 eq4021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq4021
  have eq4107 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | (have i₁ := eq4058 x
       have i₂ := eq59 sF4 x x (M.op x sF3)
       grind)
    | exact superpose eq59 eq4058
    | exact resolve eq4058 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq4058
  have eq4149 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X0) = (M.op (M.op X0 (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq2090 eq4107
    | exact resolve eq4107 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090 eq4107
  have eq5465 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op X1 y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3973 x
       have i₂ := eq14 sF0 X1 x
       grind)
    | exact superpose eq14 eq3973
    | exact resolve eq3973 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3973
  have eq6622 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op X1 (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4149 x
       have i₂ := eq14 sF4 X1 x
       grind)
    | exact superpose eq14 eq4149
    | exact resolve eq4149 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4149
  have eq24065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq24066 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq24065
    | exact resolve eq24065 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24065
  have eq24077 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq24066
       have r₂ := eq27
       grind)
    | exact resolve eq24066 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24066
  have eq24079 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq24077
    | exact resolve eq24077 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24077
  have eq24090 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24079 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq24079
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq24079
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq24079
       grind)
    | exact resolve eq13 eq24079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24079
  have eq24136 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq24090
  have eq24174 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24136 eq55
    | exact resolve eq55 eq24136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq24136
  have eq24193 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq24174
    | exact resolve eq24174 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq24174
  have eq24196 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq24193
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq24193
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq24193
       have r₂ := eq13 x y
       grind)
    | exact resolve eq24193 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24193
  have eq24198 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq24196
       grind)
    | exact superpose eq24196 eq44
    | exact resolve eq44 eq24196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq24205 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq24196
       grind)
    | exact superpose eq24196 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq24196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24196
  have eq24206 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24205
  have eq24208 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24206
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24206
    | exact resolve eq24206 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24206
  have eq24209 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24208
  have eq24216 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24198
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24198
    | exact resolve eq24198 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24198
  have eq24221 : (M.op x (M.op x y)) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq446 x
       have i₂ := eq24209
       grind)
    | exact superpose eq24209 eq446
    | exact resolve eq446 eq24209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24226 : (M.op (M.op x y) x) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61 y
       have i₂ := eq24209
       grind)
    | exact superpose eq24209 eq61
    | exact resolve eq61 eq24209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq24227 : y ≠ y ∨ x = (M.op x y) ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq24209
       grind)
    | exact superpose eq24209 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq24209
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq24209
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq24209
       grind)
    | exact resolve eq12 eq24209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24237 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 y x X1
       have i₂ := eq24209
       grind)
    | exact superpose eq24209 eq63
    | exact resolve eq63 eq24209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24209
  have eq24275 : x = (M.op x y) ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24227
  have eq24295 : x = (M.op x y) ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24275
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24275
    | exact resolve eq24275 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24275
  have eq24296 : (k y x) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24295
  have eq24320 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24216 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq24216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24216
  have eq24321 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24320
  have eq24325 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq24321
    | exact resolve eq24321 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24321
  have eq24326 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24325
  have eq24340 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24326 eq467
    | exact resolve eq467 eq24326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24345 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24326 eq62
    | exact resolve eq62 eq24326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq24346 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24326 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq24326
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq24326
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq24326
       grind)
    | exact resolve eq12 eq24326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24356 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq24326 eq63
    | exact resolve eq63 eq24326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq24326
  have eq24394 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24346
  have eq24414 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq24394
    | exact resolve eq24394 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24394
  have eq24415 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24414
  have eq24982 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq24296
       grind)
    | exact superpose eq24296 eq96
    | exact resolve eq96 eq24296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24296
  have eq25543 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24415 eq106
    | exact resolve eq106 eq24415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24415
  have eq26192 : (k (σ y) (σ x)) = (σ (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24982
       have i₂ := eq24221
       grind)
    | exact superpose eq24221 eq24982
    | exact resolve eq24982 eq24221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24221 eq24982
  have eq26220 : (k (σ y) (σ x)) = (σ (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26192
  have eq26222 : (k y x) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24340 eq25543
    | exact resolve eq25543 eq24340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24340 eq25543
  have eq26249 : (k y x) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26222
  have eq26297 : (σ (k y x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26249 eq15
    | exact resolve eq15 eq26249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26249
  have eq26326 : (k (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26297
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq26297
    | exact resolve eq26297 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26297
  have eq26683 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24226 eq24237
    | exact resolve eq24237 eq24226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24226 eq24237
  have eq26865 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq26683 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26683
  have eq26988 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26865 X0
       have i₂ := eq401 X0 y
       grind)
    | exact superpose eq401 eq26865
    | exact resolve eq26865 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26865
  have eq27214 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26988 eq26220
    | exact resolve eq26220 eq26988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26220 eq26988
  have eq27236 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27214
  have eq27249 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27236
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27236
    | exact resolve eq27236 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27236
  have eq27329 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq27249
    | exact resolve eq27249 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27249
  have eq27424 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27329 eq26326
    | exact resolve eq26326 eq27329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26326 eq27329
  have eq27426 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27424
  have eq45742 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24345 eq24356
    | exact resolve eq24356 eq24345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24345 eq24356
  have eq45955 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq45742 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45742
  have eq46109 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq403 eq45955
    | exact resolve eq45955 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45955
  have eq46407 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46109 eq27426
    | exact resolve eq27426 eq46109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27426 eq46109
  have eq46435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq46407
  have eq46471 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq46435
    | exact resolve eq46435 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46435
  have eq46574 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq46471
       have r₂ := eq27
       grind)
    | exact resolve eq46471 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46471
  have eq46654 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46574 eq51
    | (have r₁ := eq51
       have r₂ := eq46574
       grind)
    | exact resolve eq51 eq46574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq46684 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq46654
  have eq46696 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46684 eq106
    | exact resolve eq106 eq46684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq46684
  have eq46740 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq46696
    | exact resolve eq46696 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46696
  have eq46742 : y = (k y x) := by
    first
    | (have r₁ := eq46740
       have r₂ := eq50
       grind)
    | exact resolve eq46740 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq46740
  have eq46747 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq46742
       grind)
    | exact superpose eq46742 eq96
    | exact resolve eq96 eq46742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq46757 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq46742
       grind)
    | exact superpose eq46742 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq46742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46758 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq46757
  have eq46760 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46758
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq46758
    | exact resolve eq46758 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46758
  have eq46767 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq46747
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq46747
    | exact resolve eq46747 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46747
  have eq46795 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46767 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq46767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46796 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq46795
  have eq46798 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq46796
    | exact resolve eq46796 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46796
  have eq46810 : (M.op x (M.op x y)) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq446 x
       have i₂ := eq46760
       grind)
    | exact superpose eq46760 eq446
    | exact resolve eq446 eq46760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq46819 : y ≠ y ∨ x = (M.op x y) ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq46760
       grind)
    | exact superpose eq46760 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq46760
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq46760
       grind)
    | exact resolve eq12 eq46760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46760
  have eq46877 : x = (M.op x y) ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq46819
  have eq46906 : x = (M.op x y) ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46877
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq46877
    | exact resolve eq46877 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46877
  have eq46907 : x = (M.op x y) ∨ (k y x) = (M.op y y) := by grind
  clear eq46906
  have eq46921 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46907
       have i₂ := eq46742
       grind)
    | exact superpose eq46742 eq46907
    | exact resolve eq46907 eq46742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46742 eq46907
  have eq46924 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46798 eq467
    | exact resolve eq467 eq46798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq46931 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46798 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq46798
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq46798
       grind)
    | exact resolve eq12 eq46798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46989 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq46931
  have eq47016 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq46989
    | exact resolve eq46989 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46989
  have eq47017 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq47016
  have eq47031 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46767 eq47017
    | exact resolve eq47017 eq46767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46767 eq47017
  have eq47069 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq401 X0 y
       have i₂ := eq46921
       grind)
    | exact superpose eq46921 eq401
    | exact resolve eq401 eq46921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq47070 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq46921
       grind)
    | exact superpose eq46921 eq13
    | (have j0 := eq13 y y
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq46921
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq46921
       grind)
    | exact resolve eq13 eq46921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47123 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq47070
  have eq47227 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq47031 eq403
    | exact resolve eq403 eq47031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq47384 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2630 y
       have i₂ := eq47123
       grind)
    | exact superpose eq47123 eq2630
    | (have j0 := eq2630 y
       grind)
    | exact resolve eq2630 eq47123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2630 eq47123
  have eq47387 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq47384
  have eq47390 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq47387
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47387
    | exact resolve eq47387 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47387
  have eq47513 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47390 eq6622
    | exact resolve eq6622 eq47390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6622
  have eq48046 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46921
       have i₂ := eq46810
       grind)
    | exact superpose eq46810 eq46921
    | exact resolve eq46921 eq46810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46810 eq46921
  have eq48113 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq48046
  have eq48977 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46924 eq47031
    | exact resolve eq47031 eq46924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46924 eq47031
  have eq49044 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq48977
  have eq50241 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47069 eq48113
    | exact resolve eq48113 eq47069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47069 eq48113
  have eq50271 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq50241
  have eq50293 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50271
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50271
    | exact resolve eq50271 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50271
  have eq50465 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50293 eq20
    | exact resolve eq20 eq50293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50293
  have eq50639 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50465
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50465
    | exact resolve eq50465 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50465
  have eq53642 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47227 eq49044
    | exact resolve eq49044 eq47227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47227
  have eq53661 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq53642
  have eq53699 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq53661
    | exact resolve eq53661 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53661
  have eq53871 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53699 eq27
    | exact resolve eq27 eq53699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53699
  have eq61545 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46574 eq47513
    | exact resolve eq47513 eq46574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46574 eq47513
  have eq61624 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq61545
  have eq61636 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq61624
    | exact resolve eq61624 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq61624
  have eq61670 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61636 eq47390
    | exact resolve eq47390 eq61636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47390 eq61636
  have eq61738 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq61670
  have eq61826 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61738 eq27
    | exact resolve eq27 eq61738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61738
  have eq61977 : x = (M.op x y) := by
    first
    | (have r₁ := eq61826
       have r₂ := eq50639
       grind)
    | exact resolve eq61826 eq50639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50639 eq61826
  have eq61987 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq61977 eq20
    | exact resolve eq20 eq61977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq62122 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq61987
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq61987
    | exact resolve eq61987 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61987
  have eq62257 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62122 eq46798
    | exact resolve eq46798 eq62122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46798
  have eq62266 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62122 eq49044
    | exact resolve eq49044 eq62122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49044
  have eq62282 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq62266
       have r₂ := eq27
       grind)
    | exact resolve eq62266 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62266
  have eq62286 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq62257
       have r₂ := eq27
       grind)
    | exact resolve eq62257 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62257
  have eq62725 : (σ y) ≠ (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq62286 eq1291
    | exact resolve eq1291 eq62286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291 eq62286
  have eq62823 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq62725
       have r₂ := eq62282
       grind)
    | exact resolve eq62725 eq62282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62282 eq62725
  have eq63222 : (τ (σ y)) = (k y y) := by
    first
    | exact superpose eq62823 eq117
    | exact resolve eq117 eq62823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq62823
  have eq63245 : y = (k y y) := by
    first
    | exact superpose eq29 eq63222
    | exact resolve eq63222 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq63222
  have eq63411 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq63245
       grind)
    | exact superpose eq63245 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq63245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63245
  have eq63412 : y = (M.op y y) := by grind
  clear eq63411
  have eq63635 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq5465 y y
       have i₂ := eq63412
       grind)
    | exact superpose eq63412 eq5465
    | exact resolve eq5465 eq63412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5465
  have eq63661 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq61977 eq63635
    | exact resolve eq63635 eq61977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63635
  have eq63693 : y = (M.op x y) := by
    first
    | (have i₁ := eq63661
       have i₂ := eq63412
       grind)
    | exact superpose eq63412 eq63661
    | exact resolve eq63661 eq63412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63412 eq63661
  have eq63717 : y = (M.op x y) := by
    first
    | (have i₁ := eq63693
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq63693
    | exact resolve eq63693 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq63693
  have eq63731 : x = y := by
    first
    | exact superpose eq61977 eq63717
    | exact resolve eq63717 eq61977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61977 eq63717
  have eq63738 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq63731
       grind)
    | exact superpose eq63731 eq24
    | exact resolve eq24 eq63731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq63731
  have eq63941 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq63738
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq63738
    | exact resolve eq63738 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq63738
  have eq64005 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq62122 eq63941
    | exact resolve eq63941 eq62122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63941
  have eq64241 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64005 eq53871
    | (have r₁ := eq53871
       have r₂ := eq64005
       grind)
    | exact resolve eq53871 eq64005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53871 eq64005
  have eq64257 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq64241
  have eq64266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62122 eq64257
    | exact resolve eq64257 eq62122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62122 eq64257
  have eq64347 : False := by grind
  exact eq64347
