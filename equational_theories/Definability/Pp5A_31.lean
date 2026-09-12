import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  clear eq18
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq42 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq62 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (k X1 (σ X0))
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq100 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq377 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100 x y
       grind)
    | exact superpose eq100 eq16
    | (have j1 := eq100 x y
       grind)
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1853 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq377
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq377
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq377
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq377
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq377 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq1854 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1853
  have eq2177 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq386 (τ X1) (τ X0)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq386
    | (have j0 := eq386 (τ X1) (τ X0)
       grind)
    | exact resolve eq386 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq2187 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2177 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq2177
    | (have j0 := eq2177 X0 X1
       grind)
    | exact resolve eq2177 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177
  have eq2202 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2187 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2187
    | (have j0 := eq2187 X0 X1
       grind)
    | exact resolve eq2187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187
  have eq2214 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2202 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2202
    | (have j0 := eq2202 X0 X1
       grind)
    | exact resolve eq2202 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202
  have eq2220 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2214 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2214
    | (have j0 := eq2214 X0 X1
       grind)
    | exact resolve eq2214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq2224 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2220 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq2220
    | (have j0 := eq2220 X0 X1
       grind)
    | exact resolve eq2220 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2220
  have eq2228 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2224 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2224
    | (have j0 := eq2224 X0 X1
       grind)
    | exact resolve eq2224 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224
  have eq2229 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2228 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2228
    | (have j0 := eq2228 X0 X1
       grind)
    | exact resolve eq2228 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228
  have eq28923 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1854
       grind)
    | exact superpose eq1854 eq16
    | exact resolve eq16 eq1854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1854
  have eq28924 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq28923
       have r₂ := eq22 x
       grind)
    | exact resolve eq28923 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28923
  have eq29124 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 y X0 x
       have i₂ := eq28924
       grind)
    | exact superpose eq28924 eq44
    | exact resolve eq44 eq28924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28924
  have eq29151 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq29124 X0 x
       have i₂ := eq44 x x X0 x
       grind)
    | exact superpose eq44 eq29124
    | exact resolve eq29124 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29124
  have eq29465 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq62 x (σ y)
       have i₂ := eq29151 X0
       grind)
    | exact superpose eq29151 eq62
    | (have j0 := eq62 x (σ y)
       have j1 := eq29151 X0
       grind)
    | (have r₁ := eq62 x (σ y)
       have r₂ := eq29151 X0
       grind)
    | exact resolve eq62 eq29151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq29151
  have eq29501 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq29465 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29465
  have eq29502 : ∀ X0 : G, (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq29501 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29501
  have eq29521 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq29502 X0
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq29502
    | (have j0 := eq29502 X0
       grind)
    | exact resolve eq29502 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29502
  have eq30351 : ∀ X0 : G, y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq29521 X0
       grind)
    | exact superpose eq29521 eq10
    | (have j1 := eq29521 X0
       grind)
    | exact resolve eq10 eq29521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29521
  have eq30437 : ∀ X0 : G, x = y ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq30351 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30351
    | (have j0 := eq30351 X0
       grind)
    | exact resolve eq30351 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30351
  have eq30665 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq30437 X0
       grind)
    | exact superpose eq30437 eq16
    | (have j1 := eq30437 X0
       grind)
    | exact resolve eq16 eq30437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30437
  have eq30666 : ∀ X0 : G, (σ (k y x)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq30665 X0
       grind)
    | (have r₁ := eq30665 X0
       have r₂ := eq22 x
       grind)
    | exact resolve eq30665 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30665
  have eq30674 : ∀ X0 : G, (k y x) = (τ (σ (M.op x x))) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq30666 X0
       grind)
    | exact superpose eq30666 eq10
    | (have j1 := eq30666 X0
       grind)
    | exact resolve eq10 eq30666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30666
  have eq30763 : ∀ X0 : G, (k y x) = (M.op x x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq30674 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq30674
    | (have j0 := eq30674 X0
       grind)
    | exact resolve eq30674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30674
  have eq31079 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq2229 y x
       have i₂ := eq30763 X0
       grind)
    | exact superpose eq30763 eq2229
    | (have j0 := eq2229 y x
       have j1 := eq30763 x
       grind)
    | (have r₁ := eq2229 y x
       have r₂ := eq30763 X0
       grind)
    | exact resolve eq2229 eq30763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229 eq30763
  have eq31086 : ∀ X0 : G, x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq31079 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31079
  have eq31091 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq31086 X0
       grind)
    | exact superpose eq31086 eq16
    | (have j1 := eq31086 x
       grind)
    | exact resolve eq16 eq31086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31086
  have eq31092 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq31091 x
       grind)
    | (have r₁ := eq31091 X0
       have r₂ := eq22 x
       grind)
    | exact resolve eq31091 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31091
  have eq31259 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq31092 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31092
  have eq31260 : (M.op x y) = (M.op x x) := by grind
  clear eq31259
  have eq31270 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq31260
       grind)
    | exact superpose eq31260 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq31260
       grind)
    | exact resolve eq13 eq31260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31273 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 y X0 x
       have i₂ := eq31260
       grind)
    | exact superpose eq31260 eq44
    | exact resolve eq44 eq31260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31260
  have eq31299 : x = y ∨ (k y x) = (M.op x x) := by grind
  clear eq31270
  have eq31301 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq31273 X0 x
       have i₂ := eq44 x x X0 x
       grind)
    | exact superpose eq44 eq31273
    | exact resolve eq31273 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq31273
  have eq31692 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31299
       grind)
    | exact superpose eq31299 eq16
    | exact resolve eq16 eq31299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31299
  have eq31693 : (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq31692
       have r₂ := eq22 x
       grind)
    | exact resolve eq31692 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31692
  have eq31926 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq386 x y
       have i₂ := eq31693
       grind)
    | exact superpose eq31693 eq386
    | (have j0 := eq386 x y
       grind)
    | exact resolve eq386 eq31693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq31693
  have eq31936 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq31926
  have eq35783 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31936
       grind)
    | exact superpose eq31936 eq16
    | exact resolve eq16 eq31936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31936
  have eq35854 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq35783
       have i₂ := eq31301 x
       grind)
    | exact superpose eq31301 eq35783
    | exact resolve eq35783 eq31301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35783
  have eq35855 : (σ x) = (σ y) := by grind
  clear eq35854
  have eq36153 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35855
       grind)
    | exact superpose eq35855 eq16
    | exact resolve eq16 eq35855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35855
  have eq36270 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq36153
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq36153
    | exact resolve eq36153 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq36153
  have eq36280 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq36270
       have i₂ := eq31301 x
       grind)
    | exact superpose eq31301 eq36270
    | exact resolve eq36270 eq31301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31301 eq36270
  have eq36281 : False := by grind
  exact eq36281

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation3607 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3607 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq42 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq42 (σ X0)
       grind)
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq56
    | exact resolve eq56 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq56
  have eq79 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq79
    | (have j0 := eq79 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq79 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq222 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq150
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq150
    | (have j1 := eq79 (σ x) (σ y)
       grind)
    | (have r₁ := eq150
       have r₂ := eq79 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq150
       have r₂ := eq79 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq150 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq150
  have eq225 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq222
  have eq226 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq225
       grind)
    | exact superpose eq225 eq16
    | exact resolve eq16 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq227 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq226
       have r₂ := eq65 x
       grind)
    | exact resolve eq226 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq263 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq227
       grind)
    | exact superpose eq227 eq10
    | exact resolve eq10 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq280 : x = y := by
    first
    | (have i₁ := eq263
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq263
    | exact resolve eq263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq324 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq280
       grind)
    | exact superpose eq280 eq16
    | exact resolve eq16 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq325 : False := by grind
  exact eq325

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation3607 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3607 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq85 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) := by
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
  have eq86 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38411 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38412 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq38411
    | exact resolve eq38411 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38411
  have eq38424 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq38412
       have r₂ := eq28
       grind)
    | exact resolve eq38412 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38412
  have eq38428 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq38424
    | exact resolve eq38424 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38424
  have eq38433 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq38428 eq86
    | (have r₁ := eq86
       have r₂ := eq38428
       grind)
    | exact resolve eq86 eq38428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq38428
  have eq38511 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq38433
  have eq38512 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq38511
  have eq38547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq38512 eq77
    | exact resolve eq77 eq38512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq38512
  have eq38561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq38547
  have eq38564 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq38561
       have r₂ := eq28
       grind)
    | exact resolve eq38561 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38561
  have eq38566 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq38564
       grind)
    | exact superpose eq38564 eq52
    | exact resolve eq52 eq38564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq38568 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq38564
       grind)
    | exact superpose eq38564 eq85
    | (have r₁ := eq85
       have r₂ := eq38564
       grind)
    | exact resolve eq85 eq38564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq38564
  have eq38645 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq38568
  have eq38646 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq38645
  have eq38676 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq38566
    | exact resolve eq38566 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38566
  have eq39062 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq38646
       grind)
    | exact superpose eq38646 eq49
    | exact resolve eq49 eq38646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq38646
  have eq39088 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq39062
    | exact resolve eq39062 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39062
  have eq39284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39088 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq39088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39088
  have eq39285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq39284
  have eq39289 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq39285
    | exact resolve eq39285 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39285
  have eq39301 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq39289
       have r₂ := eq28
       grind)
    | exact resolve eq39289 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39289
  have eq39305 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq39301
    | exact resolve eq39301 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39301
  have eq39673 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq39305 eq38676
    | exact resolve eq38676 eq39305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38676 eq39305
  have eq39749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq39673
  have eq39772 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq39749
       have r₂ := eq28
       grind)
    | exact resolve eq39749 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39749
  have eq39787 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq39772 eq30
    | exact resolve eq30 eq39772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq39772
  have eq39904 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq39787
    | exact resolve eq39787 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq39787
  have eq39905 : x = y := by grind
  clear eq39904
  have eq39924 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq39905
       grind)
    | exact superpose eq39905 eq19
    | exact resolve eq19 eq39905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq39925 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq39905
       grind)
    | exact superpose eq39905 eq25
    | exact resolve eq25 eq39905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq39905
  have eq40041 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq39925
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39925
    | exact resolve eq39925 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq39925
  have eq41059 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40041 eq27
    | exact resolve eq27 eq40041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq40041
  have eq41383 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq41059 eq68
    | exact resolve eq68 eq41059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq41059
  have eq41502 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq41383
       have i₂ := eq39924
       grind)
    | exact superpose eq39924 eq41383
    | exact resolve eq41383 eq39924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39924 eq41383
  have eq41541 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41502 eq15
    | exact resolve eq15 eq41502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41502
  have eq41587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq41541
    | exact resolve eq41541 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq41541
  have eq41596 : False := by grind
  exact eq41596

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyy_pxy_pxx_pxy_Equation3698 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
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
  have eq50 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X3 X4) (M.op X3 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X2 X3 X4
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 X3) (M.op X2 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X2 X3) (M.op X2 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x X0)) := by
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
  have eq59 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq76
    | (have j0 := eq76 (σ X0) (σ X1)
       grind)
    | exact resolve eq76 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq44
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq121 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) ≠ (M.op X3 X2) ∨ (M.op X3 X2) = X3 ∨ (M.op X3 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq123 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq123 x
       have r₂ := eq13 x x
       grind)
    | exact resolve eq123 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq129 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq125 (σ X0)
       grind)
    | exact superpose eq125 eq10
    | exact resolve eq10 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq83
       have i₂ := eq125 y
       grind)
    | exact superpose eq125 eq83
    | exact resolve eq83 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq134 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq131
       have i₂ := eq125 sF3
       grind)
    | exact superpose eq125 eq131
    | exact resolve eq131 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq136 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq129 X0
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq129
    | exact resolve eq129 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq151 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq154 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq151
       have i₂ := eq125 sF1
       grind)
    | exact superpose eq125 eq151
    | exact resolve eq151 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq157 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq154
       have i₂ := eq125 sF0
       grind)
    | exact superpose eq125 eq154
    | exact resolve eq154 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq154
  have eq264 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op x y) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq54 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op x y) (M.op x X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y y)) := by
    first
    | exact superpose eq266 eq157
    | exact resolve eq157 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq290 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq281
       have i₂ := eq134
       grind)
    | exact superpose eq134 eq281
    | exact resolve eq281 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq337 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq290 eq59
    | exact resolve eq59 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq680 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 X3
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq807 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) x
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq14
    | exact resolve eq14 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1312 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 X3) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X4 X5) (M.op X6 X3))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq51 X3 X6 (M.op X4 X5) (M.op X4 X2)
       have i₂ := eq50 X4 X5 X2 X0 X1
       grind)
    | (have i₁ := eq51 X3 X6 (M.op X4 X5) (M.op X4 X2)
       have i₂ := eq50 X0 X1 X2 X4 X5
       grind)
    | exact superpose eq50 eq51
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq51
  have eq1384 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq105 eq76
    | (have j0 := eq76 (σ x) (σ y)
       grind)
    | exact resolve eq76 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1385 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq1384
    | exact resolve eq1384 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq1388 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq1385
       have r₂ := eq27
       grind)
    | exact resolve eq1385 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq1390 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq290 eq1388
    | exact resolve eq1388 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq1392 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq1390
    | exact resolve eq1390 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq2487 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq136 X1
       grind)
    | exact superpose eq136 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq136
  have eq2528 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2487 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2487
    | (have j0 := eq2487 X0 y
       grind)
    | exact resolve eq2487 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2487
  have eq2594 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2528 X0
       have i₂ := eq134
       grind)
    | exact superpose eq134 eq2528
    | (have j0 := eq2528 X0
       grind)
    | exact resolve eq2528 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528
  have eq2623 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq290 eq2594
    | (have j0 := eq2594 X0
       grind)
    | exact resolve eq2594 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594
  have eq2890 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ≠ (M.op X1 (σ y)) ∨ (M.op X1 (σ y)) = X1 ∨ (M.op X1 X1) = (k X1 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq121
    | (have j0 := eq121 (σ x) X0 (σ y) X1
       grind)
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq2962 : ∀ X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op X1 (σ y)) ∨ (M.op X1 (σ y)) = X1 ∨ (M.op X1 X1) = (k X1 (σ y)) := by
    intro X1
    first
    | exact superpose eq337 eq2890
    | (have j0 := eq2890 x X1
       grind)
    | exact resolve eq2890 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890
  have eq62754 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k (τ X0) y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2623 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2623
    | exact resolve eq2623 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2623
  have eq62877 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62754 X0
       have i₂ := eq34 X0 y
       grind)
    | exact superpose eq34 eq62754
    | (have j0 := eq62754 X0
       grind)
    | exact resolve eq62754 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq62754
  have eq62900 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62877 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq62877
    | (have j0 := eq62877 X0
       grind)
    | exact resolve eq62877 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq62877
  have eq74416 : ∀ X2 X3 X4 X5 X6 : G, (M.op X3 X3) = (M.op (M.op (M.op x y) (M.op x X2)) (M.op (M.op X4 X5) (M.op X6 X3))) := by
    intro X2 X3 X4 X5 X6
    first
    | (have i₁ := eq1312 x x X2 X3 X4 X5 X6
       have i₂ := eq264 x x X2
       grind)
    | (have i₁ := eq1312 x y X2 X3 X4 X5 X6
       have i₂ := eq264 x x X2
       grind)
    | exact superpose eq264 eq1312
    | (have j0 := eq1312 x y X2 X3 X4 X5 X6
       grind)
    | exact resolve eq1312 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq1312
  have eq77387 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq2962
    | (have j0 := eq2962 (σ x)
       grind)
    | exact resolve eq2962 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2962
  have eq86548 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq267 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq267
    | (have j0 := eq267 y x
       grind)
    | exact resolve eq267 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq267
  have eq86558 : (M.op x y) ≠ (M.op y y) ∨ x = (M.op x y) ∨ (k x y) = (M.op x x) := by
    first
    | exact superpose eq266 eq86548
    | exact resolve eq86548 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq86548
  have eq708063 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1392 eq77387
    | (have r₁ := eq77387
       have r₂ := eq1392
       grind)
    | exact resolve eq77387 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77387
  have eq708064 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq708063
  have eq708072 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq708064 eq105
    | exact resolve eq105 eq708064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708064
  have eq708099 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq708072
  have eq708497 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op X1 X2) (σ (M.op x y)))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq708099 eq74416
    | exact resolve eq74416 eq708099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74416 eq708099
  have eq708684 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq680 eq708497
    | exact resolve eq708497 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq708497
  have eq709582 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq708684 eq1392
    | exact resolve eq1392 eq708684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392 eq708684
  have eq710304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq709582
  have eq710384 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq710304
       have r₂ := eq27
       grind)
    | exact resolve eq710304 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710304
  have eq710400 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq134
       have i₂ := eq710384
       grind)
    | exact superpose eq710384 eq134
    | exact resolve eq134 eq710384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710384
  have eq710726 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq290 eq710400
    | exact resolve eq710400 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710400
  have eq710751 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq710726
    | exact resolve eq710726 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710726
  have eq715123 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq62900 eq710751
    | (have j1 := eq62900 X0
       grind)
    | exact resolve eq710751 eq62900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62900 eq710751
  have eq3398376 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq715123 eq65
    | (have j1 := eq715123 (σ x)
       grind)
    | exact resolve eq65 eq715123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715123
  have eq3398788 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3398376
    | exact resolve eq3398376 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398376
  have eq3398821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3398788
    | exact resolve eq3398788 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3398788
  have eq3398833 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3398821
       have r₂ := eq27
       grind)
    | exact resolve eq3398821 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398821
  have eq3398842 : (k (σ x) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq3398833
       grind)
    | exact superpose eq3398833 eq44
    | exact resolve eq44 eq3398833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq3398833
  have eq3398948 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3398842
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq3398842
    | exact resolve eq3398842 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398842
  have eq3398989 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq3398948
       have r₂ := eq74
       grind)
    | exact resolve eq3398948 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq3398948
  have eq3399060 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3398989 eq65
    | exact resolve eq65 eq3398989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq3399061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq3398989 eq105
    | exact resolve eq105 eq3398989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq3398989
  have eq3399151 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq3399061
       have r₂ := eq27
       grind)
    | exact resolve eq3399061 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3399061
  have eq3399171 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq134
       have i₂ := eq3399151
       grind)
    | exact superpose eq3399151 eq134
    | exact resolve eq134 eq3399151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq3399197 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq86558
       have i₂ := eq3399151
       grind)
    | exact superpose eq3399151 eq86558
    | (have r₁ := eq86558
       have r₂ := eq3399151
       grind)
    | exact resolve eq86558 eq3399151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86558 eq3399151
  have eq3399981 : x = (M.op x y) ∨ (k x y) = (M.op x x) := by grind
  clear eq3399197
  have eq3400205 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq290 eq3399171
    | exact resolve eq3399171 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq3399171
  have eq3400314 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq3400205
    | exact resolve eq3400205 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3400205
  have eq3936365 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3399981
       have i₂ := eq3399060
       grind)
    | exact superpose eq3399060 eq3399981
    | exact resolve eq3399981 eq3399060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3399981
  have eq3936549 : ∀ X0 : G, (σ (τ (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) X0) (σ (τ (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq807 x x
       have i₂ := eq3936365
       grind)
    | exact superpose eq3936365 eq807
    | exact resolve eq807 eq3936365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807 eq3936365
  have eq3937694 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3936549 X0
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq3936549
    | exact resolve eq3936549 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3936549
  have eq3937867 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3937694 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3937694
    | (have j0 := eq3937694 X0
       grind)
    | exact resolve eq3937694 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937694
  have eq3937961 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq337 eq3937867
    | exact resolve eq3937867 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq3937867
  have eq3937997 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3400314 eq3937961
    | exact resolve eq3937961 eq3400314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3400314 eq3937961
  have eq3938027 : x = (M.op x y) := by
    first
    | (have r₁ := eq3937997
       have r₂ := eq27
       grind)
    | exact resolve eq3937997 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937997
  have eq3938063 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3938027 eq20
    | exact resolve eq20 eq3938027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq3938068 : x ≠ x ∨ x = (k x y) := by
    first
    | exact superpose eq3938027 eq73
    | (have r₁ := eq73
       have r₂ := eq3938027
       grind)
    | exact resolve eq73 eq3938027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq3938027
  have eq3940293 : x = (k x y) := by grind
  clear eq3938068
  have eq3941297 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3940293
       have i₂ := eq3399060
       grind)
    | exact superpose eq3399060 eq3940293
    | exact resolve eq3940293 eq3399060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3399060 eq3940293
  have eq3941301 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3938063
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3938063
    | exact resolve eq3938063 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3938063
  have eq3943026 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3941297 eq15
    | exact resolve eq15 eq3941297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3941297
  have eq3943523 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3943026
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3943026
    | exact resolve eq3943026 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3943026
  have eq3943618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3941301 eq3943523
    | exact resolve eq3943523 eq3941301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3941301 eq3943523
  have eq3943680 : False := by grind
  exact eq3943680

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq12 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq14 (M.op X1 X0) (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq53
    | (have j0 := eq53 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq53 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq53 (τ X1) (τ X0)
       grind)
    | exact superpose eq53 eq44
    | (have j1 := eq53 (τ X0) (τ X1)
       grind)
    | exact resolve eq44 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq53
  have eq552 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 x y
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq723 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq40 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq916 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq42 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq921 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq916 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq916
    | exact resolve eq916 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq943 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq921 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq921
    | exact resolve eq921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq973 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq943 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq943
    | exact resolve eq943 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq1045 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq723 X0
       have i₂ := eq973 X0
       grind)
    | exact superpose eq973 eq723
    | exact resolve eq723 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq973
  have eq208017 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1
       have i₂ := eq79 X0 X1
       grind)
    | (have i₁ := eq11 X0
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq11
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq11 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq208114 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq208017 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq208017
    | (have j0 := eq208017 X0 X1
       grind)
    | exact resolve eq208017 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208017
  have eq208191 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq208114 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq208114
    | (have j0 := eq208114 (τ (k (σ X0) X1)) (M.op (τ X1) X0)
       grind)
    | exact resolve eq208114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208114
  have eq208588 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq208191 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq208191
    | (have j0 := eq208191 X0 X1
       grind)
    | exact resolve eq208191 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq208191
  have eq208624 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq208588 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq208588
    | (have j0 := eq208588 X0 (σ X1)
       grind)
    | exact resolve eq208588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208588
  have eq208771 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq552
       have i₂ := eq208624 x y
       grind)
    | exact superpose eq208624 eq552
    | (have j1 := eq208624 x y
       grind)
    | (have r₁ := eq552
       have r₂ := eq208624 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq552
       have r₂ := eq208624 (k y x) (M.op x y)
       grind)
    | exact resolve eq552 eq208624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq208624
  have eq208772 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq208771
  have eq208773 : (σ x) = (σ y) := by grind
  clear eq208772
  have eq210473 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq208773
       grind)
    | exact superpose eq208773 eq10
    | exact resolve eq10 eq208773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208773
  have eq210576 : x = y := by
    first
    | (have i₁ := eq210473
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq210473
    | exact resolve eq210473 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210473
  have eq210609 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq210576
       grind)
    | exact superpose eq210576 eq16
    | exact resolve eq16 eq210576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210576
  have eq210610 : False := by grind
  exact eq210610

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation3698 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq953 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq957 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8153 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq953
       grind)
    | exact superpose eq953 eq39
    | exact resolve eq39 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq8154 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq8153
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8153
    | exact resolve eq8153 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8153
  have eq8156 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20 eq8154
    | exact resolve eq8154 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8154
  have eq12146 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq8156 eq957
    | exact resolve eq957 eq8156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12153 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq12146
       have r₂ := eq27
       grind)
    | exact resolve eq12146 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12146
  have eq12160 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq12153 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12153
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12153
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12153
       grind)
    | exact resolve eq12 eq12153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12153
  have eq12187 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq12160
  have eq12210 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq12187
       have r₂ := eq26
       grind)
    | exact resolve eq12187 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12187
  have eq12225 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq8156 eq12210
    | exact resolve eq12210 eq8156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8156 eq12210
  have eq12234 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12225
       have r₂ := eq27
       grind)
    | exact resolve eq12225 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12225
  have eq12244 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq12234
       grind)
    | exact superpose eq12234 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12234
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12234
       grind)
    | exact resolve eq12 eq12234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12234
  have eq12271 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq12244
  have eq12296 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12271
       have r₂ := eq18
       grind)
    | exact resolve eq12271 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12271
  have eq12550 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq12296
       grind)
    | exact superpose eq12296 eq39
    | exact resolve eq39 eq12296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12296
  have eq12551 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12550
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12550
    | exact resolve eq12550 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12550
  have eq12553 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq12551
    | exact resolve eq12551 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12551
  have eq12562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12553 eq957
    | exact resolve eq957 eq12553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq12566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12562
  have eq12571 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12566
       have r₂ := eq27
       grind)
    | exact resolve eq12566 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12566
  have eq12586 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12571 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12571
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12571
       grind)
    | exact resolve eq12 eq12571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12571
  have eq12615 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq12586
  have eq12638 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq12615
       have r₂ := eq26
       grind)
    | exact resolve eq12615 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12615
  have eq12653 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq12553 eq12638
    | exact resolve eq12638 eq12553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12553 eq12638
  have eq12662 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12653
       have r₂ := eq27
       grind)
    | exact resolve eq12653 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12653
  have eq12668 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq12662 eq31
    | exact resolve eq31 eq12662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq12662
  have eq12698 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq12668
    | exact resolve eq12668 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12668
  have eq12699 : x = y := by grind
  clear eq12698
  have eq12702 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12699
       grind)
    | exact superpose eq12699 eq18
    | exact resolve eq18 eq12699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq12703 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq12699
       grind)
    | exact superpose eq12699 eq24
    | exact resolve eq24 eq12699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq12699
  have eq12712 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq12703
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12703
    | exact resolve eq12703 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12703
  have eq12713 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq12702
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq12702
    | exact resolve eq12702 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12702
  have eq12714 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12712 eq26
    | exact resolve eq26 eq12712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq12712
  have eq12744 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq12714
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq12714
    | exact resolve eq12714 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq12714
  have eq12753 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq12713
       grind)
    | exact superpose eq12713 eq39
    | exact resolve eq39 eq12713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq12713
  have eq12795 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq12753
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12753
    | exact resolve eq12753 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12753
  have eq12800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12744 eq12795
    | exact resolve eq12795 eq12744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12744 eq12795
  have eq12802 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq12800
    | exact resolve eq12800 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq12800
  have eq12804 : False := by grind
  exact eq12804

/-- `Equation3803`: `x ◇ y = (z ◇ y) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_y_pyx_Equation3803 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3803 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3803.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  clear eq41
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
  have eq175 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x y) (M.op X0 y)) := by
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
  have eq176 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq178 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 x
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq188 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq183 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq183
       grind)
    | exact resolve eq13 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq179
    | (have j0 := eq179 (σ x)
       grind)
    | exact resolve eq179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq192 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (k X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq189 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq189
       grind)
    | exact resolve eq13 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq188 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq509 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq183 eq508
    | exact resolve eq508 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq508
  have eq511 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq509 eq42
    | exact resolve eq42 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq509
  have eq512 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq511
    | exact resolve eq511 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq520 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have j0 := eq192 (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq521 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq189 eq520
    | exact resolve eq520 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq520
  have eq620 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq657 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq620
       grind)
    | exact superpose eq620 eq40
    | exact resolve eq40 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq688 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq687
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq687
    | exact resolve eq687 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq690 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq688
    | exact resolve eq688 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq698 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq690 eq621
    | exact resolve eq621 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq698
       have r₂ := eq27
       grind)
    | exact resolve eq698 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq716 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq705 eq521
    | exact resolve eq521 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq730 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq716 eq153
    | exact resolve eq153 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq716
  have eq731 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq730
    | exact resolve eq730 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq730
  have eq1066 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq648 y y
       have i₂ := eq731
       grind)
    | exact superpose eq731 eq648
    | (have j0 := eq648 y y
       grind)
    | (have r₁ := eq648 y y
       have r₂ := eq731
       grind)
    | exact resolve eq648 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq1081 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq1066
  have eq1122 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq1081
       grind)
    | exact superpose eq1081 eq175
    | exact resolve eq175 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq1081
  have eq1643 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq705 eq660
    | (have r₁ := eq660
       have r₂ := eq705
       grind)
    | exact resolve eq660 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq705
  have eq1644 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1643
  have eq1645 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq690 eq1644
    | exact resolve eq1644 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq1647 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1645 eq182
    | exact resolve eq182 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1655 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1647
    | exact resolve eq1647 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq1656 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq690 eq1655
    | exact resolve eq1655 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq1655
  have eq1657 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1656
       have r₂ := eq27
       grind)
    | exact resolve eq1656 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1656
  have eq1658 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1657 eq29
    | exact resolve eq29 eq1657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1657
  have eq1689 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1658
    | exact resolve eq1658 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1658
  have eq1697 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1689
       grind)
    | exact superpose eq1689 eq18
    | exact resolve eq18 eq1689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1698 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1689
       grind)
    | exact superpose eq1689 eq24
    | exact resolve eq24 eq1689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1703 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq657
       have i₂ := eq1689
       grind)
    | exact superpose eq1689 eq657
    | (have r₁ := eq657
       have r₂ := eq1689
       grind)
    | exact resolve eq657 eq1689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657 eq1689
  have eq1704 : (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq1703
  have eq1707 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1698
    | exact resolve eq1698 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq1782 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1707 eq512
    | exact resolve eq512 eq1707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1846 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1782 eq648
    | (have j0 := eq648 (σ y) (σ y)
       grind)
    | (have r₁ := eq648 (σ y) (σ y)
       have r₂ := eq1782
       grind)
    | exact resolve eq648 eq1782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648 eq1782
  have eq1847 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1846
  have eq1859 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1847 eq176
    | exact resolve eq176 eq1847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq1847
  have eq2474 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq1704
       grind)
    | exact superpose eq1704 eq182
    | exact resolve eq182 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq1704
  have eq2486 : (M.op x y) = (k (M.op x y) x) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1697 eq2474
    | exact resolve eq2474 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697 eq2474
  have eq2512 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2486 eq40
    | exact resolve eq40 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2486
  have eq2519 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2512
    | exact resolve eq2512 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512
  have eq2521 : (σ y) = (k (σ y) (σ x)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1707 eq2519
    | exact resolve eq2519 eq1707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519
  have eq2544 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2521 eq621
    | exact resolve eq621 eq2521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521
  have eq2559 : x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2544
  have eq2573 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2559 eq38
    | exact resolve eq38 eq2559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq2559
  have eq2579 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2573
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2573
    | exact resolve eq2573 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2573
  have eq2581 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1707 eq2579
    | exact resolve eq2579 eq1707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579
  have eq2588 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2581 eq621
    | exact resolve eq621 eq2581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2581
  have eq2601 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2588
  have eq2614 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2601 eq27
    | exact resolve eq27 eq2601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2601
  have eq2630 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2614
       have r₂ := eq1707
       grind)
    | exact resolve eq2614 eq1707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2614
  have eq2633 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2630 eq27
    | exact resolve eq27 eq2630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2643 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2630 eq1859
    | exact resolve eq1859 eq2630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859
  have eq2652 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2643
  have eq2655 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2652
    | exact resolve eq2652 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2652
  have eq2657 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2630 eq2655
    | exact resolve eq2655 eq2630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2630 eq2655
  have eq2659 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1707 eq2633
    | exact resolve eq2633 eq1707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707 eq2633
  have eq2662 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq2659
  have eq2663 : x = (M.op x y) := by
    first
    | (have r₁ := eq2662
       have r₂ := eq2657
       grind)
    | exact resolve eq2662 eq2657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2657 eq2662
  have eq2664 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2663
       grind)
    | exact superpose eq2663 eq18
    | exact resolve eq18 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2665 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq2663
       grind)
    | exact superpose eq2663 eq22
    | exact resolve eq22 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2663
  have eq2686 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2665 eq20
    | exact resolve eq20 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2730 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2686 eq512
    | exact resolve eq512 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq2786 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2664 eq1122
    | exact resolve eq1122 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122 eq2664
  have eq2799 : y = (M.op x y) := by grind
  clear eq2786
  have eq2805 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2799
       grind)
    | exact superpose eq2799 eq24
    | exact resolve eq24 eq2799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2799
  have eq2816 : (σ x) = (σ y) := by
    first
    | exact superpose eq2665 eq2805
    | exact resolve eq2805 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2665 eq2805
  have eq2831 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2816 eq621
    | exact resolve eq621 eq2816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq2816
  have eq2867 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2730 eq2831
    | exact resolve eq2831 eq2730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2730 eq2831
  have eq2868 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2867
  have eq2897 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq2868 eq27
    | exact resolve eq27 eq2868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2868
  have eq2915 : False := by grind
  exact eq2915

/-- `Equation3868`: `x ◇ x = (x ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation3868 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3868 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3868.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq127 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq83 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq83 X1 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq130 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq130 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq133 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq131
    | (have j0 := eq131 X0 X1
       grind)
    | exact resolve eq131 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq137 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       have j1 := eq129 X1 X0
       grind)
    | (have r₁ := eq133 X1 X0
       have r₂ := eq129 X0 X1
       grind)
    | (have r₁ := eq133 (k X1 X0) X1
       have r₂ := eq129 X0 X1
       grind)
    | (have r₁ := eq133 X1 X1
       have r₂ := eq129 X1 X1
       grind)
    | exact resolve eq133 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq133
  have eq544 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq137
    | exact resolve eq137 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq137 y x
       grind)
    | exact superpose eq137 eq16
    | (have j1 := eq137 y x
       grind)
    | exact resolve eq16 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq575 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq544
    | (have j0 := eq544 X0 X1
       grind)
    | exact resolve eq544 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq544
  have eq580 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq575 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq575
    | exact resolve eq575 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq647 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq580 (τ X1) X0
       grind)
    | exact superpose eq580 eq18
    | (have j1 := eq580 (τ X1) X0
       grind)
    | exact resolve eq18 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq580
  have eq829 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq647 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq647
    | exact resolve eq647 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq881 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq829
    | (have j0 := eq829 X0 X1
       grind)
    | exact resolve eq829 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq988 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq558
       have i₂ := eq881 y x
       grind)
    | exact superpose eq881 eq558
    | (have j1 := eq881 (σ y) (σ x)
       grind)
    | (have r₁ := eq558
       have r₂ := eq881 y x
       grind)
    | exact resolve eq558 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq989 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq988
  have eq1023 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq989
  have eq1037 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq558
       have i₂ := eq1023
       grind)
    | exact superpose eq1023 eq558
    | exact resolve eq558 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq1023
  have eq1038 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1037
  have eq1039 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1038
  have eq1091 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1039
  have eq1107 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1091
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1091
    | exact resolve eq1091 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1112 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1107
       grind)
    | exact superpose eq1107 eq16
    | exact resolve eq16 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1154 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1112
       have i₂ := eq881 y x
       grind)
    | exact superpose eq881 eq1112
    | (have j1 := eq881 y x
       grind)
    | (have r₁ := eq1112
       have r₂ := eq881 y x
       grind)
    | exact resolve eq1112 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq1155 : y = (M.op x x) := by grind
  clear eq1154
  have eq1160 : (M.op x y) = (k y x) := by grind
  clear eq1155
  have eq1204 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1112
       have i₂ := eq1160
       grind)
    | exact superpose eq1160 eq1112
    | exact resolve eq1112 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq1160
  have eq1207 : False := by grind
  exact eq1207
