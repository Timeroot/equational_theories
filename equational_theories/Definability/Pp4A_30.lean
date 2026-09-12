import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq62 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq79 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X4) X3) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (M.op X0 X1) X0 X1 (M.op (M.op X0 (M.op X0 X1)) X2)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 (M.op X0 X1)) X2
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) X5)) X1) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X0 X5
       have i₂ := eq25 X3 X2 X4 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq97 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq79 (M.op X0 X1)
       grind)
    | exact superpose eq79 eq24
    | exact resolve eq24 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq99 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq9
    | exact resolve eq9 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq79 (τ X0)
       grind)
    | exact superpose eq79 eq34
    | exact resolve eq34 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq232 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq231 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq231
    | exact resolve eq231 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq249 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq232 (σ X0)
       grind)
    | exact superpose eq232 eq23
    | exact resolve eq23 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq251 : ∀ X0 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq249 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq249
    | exact resolve eq249 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq267 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq251 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq251
    | exact resolve eq251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq330 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq267 (σ X0)
       grind)
    | exact superpose eq267 eq23
    | exact resolve eq23 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq332 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq330 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq330
    | exact resolve eq330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq354 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq354 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq359 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq355 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq355
    | (have j0 := eq355 X0
       grind)
    | exact resolve eq355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq382 : ∀ X0 : G, (τ (σ X0)) = (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (τ (M.op (σ (σ X0)) (σ (σ X0)))) X0
       have i₂ := eq332 (σ X0)
       grind)
    | exact superpose eq332 eq23
    | exact resolve eq23 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 : G, (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq382 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq382
    | exact resolve eq382 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq994 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq86 X0 X1 X2 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq86
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1012 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq994 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq994
    | exact resolve eq994 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1025 : ∀ X0 X1 X2 : G, (M.op (M.op (τ X0) (τ X0)) X2) = (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X2)) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 (τ X0) X1 X2
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq90
    | (have j1 := eq62 X0 X1
       grind)
    | exact resolve eq90 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq90
  have eq1884 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) (M.op X0 X4)) (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq95 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X1 X0 X2 X4
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq95
    | exact resolve eq95 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1923 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op X0 X3) (M.op X0 X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1884 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq1884
    | exact resolve eq1884 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884
  have eq3583 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq10
    | (have j1 := eq359 X0
       grind)
    | exact resolve eq10 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq11038 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq3583
  have eq11118 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11038 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq11038
    | (have j0 := eq11038 X0
       grind)
    | exact resolve eq11038 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11038
  have eq11119 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq11118 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11118
  have eq11430 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq11119 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11119
    | exact resolve eq11119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11459 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq79 (τ X0)
       have i₂ := eq11119 X0
       grind)
    | exact superpose eq11119 eq79
    | exact resolve eq79 eq11119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11544 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq11430 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq11430
    | exact resolve eq11430 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11430
  have eq11553 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq11544 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11544
    | exact resolve eq11544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11544
  have eq11759 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq11553 (σ X0)
       grind)
    | exact superpose eq11553 eq15
    | exact resolve eq15 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11809 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11759 X0
       have i₂ := eq11553 X0
       grind)
    | exact superpose eq11553 eq11759
    | exact resolve eq11759 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11759
  have eq12704 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq11459 X0
       have i₂ := eq11553 X0
       grind)
    | exact superpose eq11553 eq11459
    | exact resolve eq11459 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11459
  have eq13359 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq79 (σ X0)
       have i₂ := eq11809 X0
       grind)
    | exact superpose eq11809 eq79
    | exact resolve eq79 eq11809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13361 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99 (σ X0) X1
       have i₂ := eq11809 X0
       grind)
    | exact superpose eq11809 eq99
    | exact resolve eq99 eq11809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25392 : ∀ X0 X1 X2 : G, (M.op (τ (k X0 X0)) X2) = (M.op (τ X0) (M.op (τ (k X0 X0)) X2)) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1025 X0 X1 X2
       have i₂ := eq11119 X0
       grind)
    | exact superpose eq11119 eq1025
    | (have j0 := eq1025 X0 X1 X2
       grind)
    | exact resolve eq1025 eq11119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq25393 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) X2) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) X2)) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25392 X0 X1 X2
       have i₂ := eq11553 X0
       grind)
    | exact superpose eq11553 eq25392
    | (have j0 := eq25392 X0 X1 X2
       grind)
    | exact resolve eq25392 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25392
  have eq25452 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq25393 X0 X1 (τ X0)
       grind)
    | exact superpose eq25393 eq97
    | (have j1 := eq25393 X0 X1 x
       grind)
    | exact resolve eq97 eq25393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25393
  have eq25521 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25452 X0 X1
       have i₂ := eq12704 X0
       grind)
    | exact superpose eq12704 eq25452
    | (have j0 := eq25452 X0 X1
       grind)
    | exact resolve eq25452 eq12704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12704 eq25452
  have eq25549 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25521 X0 X1
       have i₂ := eq11119 X0
       grind)
    | exact superpose eq11119 eq25521
    | (have j0 := eq25521 X0 X1
       grind)
    | exact resolve eq25521 eq11119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25521
  have eq25569 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25549 X0 X1
       have i₂ := eq11553 X0
       grind)
    | exact superpose eq11553 eq25549
    | (have j0 := eq25549 X0 X1
       grind)
    | exact resolve eq25549 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25549
  have eq1517089 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq332 X0
       have i₂ := eq25569 (σ X0) X1
       grind)
    | exact superpose eq25569 eq332
    | (have j1 := eq25569 (σ X0) X1
       grind)
    | exact resolve eq332 eq25569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1517090 : ∀ X0 X1 : G, (k (τ (τ (σ (σ X0)))) X0) = X0 ∨ (k (σ (σ X0)) (σ X1)) = (σ (M.op (τ (σ (σ X0))) X1)) ∨ (M.op X1 X1) = (τ (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq385 X0
       have i₂ := eq25569 (σ (σ X0)) X1
       grind)
    | exact superpose eq25569 eq385
    | (have j1 := eq25569 (σ (σ X0)) X1
       grind)
    | exact resolve eq385 eq25569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq1517097 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq25569 X0 X1
       grind)
    | exact superpose eq25569 eq11
    | (have j1 := eq25569 X0 X1
       grind)
    | exact resolve eq11 eq25569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25569
  have eq1517454 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = X0 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1517097 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1517097
    | (have j0 := eq1517097 X0 X1
       grind)
    | exact resolve eq1517097 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517097
  have eq1517461 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = X0 ∨ (k (σ (σ X0)) (σ X1)) = (σ (M.op (τ (σ (σ X0))) X1)) ∨ (M.op X1 X1) = (τ (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1517090 X0 X1
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq1517090
    | (have j0 := eq1517090 X0 X1
       grind)
    | exact resolve eq1517090 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517090
  have eq1517462 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1517089 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1517089
    | (have j0 := eq1517089 X0 X1
       grind)
    | exact resolve eq1517089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517089
  have eq1517519 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k (σ (σ X0)) (σ X1)) = (σ (M.op (τ (σ (σ X0))) X1)) ∨ (M.op X1 X1) = (τ (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1517461 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1517461
    | (have j0 := eq1517461 X0 X1
       grind)
    | exact resolve eq1517461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517461
  have eq1517520 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1517462 X0 X1
       have i₂ := eq11553 X0
       grind)
    | exact superpose eq11553 eq1517462
    | (have j0 := eq1517462 X0 X1
       grind)
    | exact resolve eq1517462 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517462
  have eq1517548 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ (σ X0)) (σ X1)) = (σ (M.op (τ (σ (σ X0))) X1)) ∨ (M.op X1 X1) = (τ (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1517519 X0 X1
       have i₂ := eq11553 X0
       grind)
    | exact superpose eq11553 eq1517519
    | (have j0 := eq1517519 X0 X1
       grind)
    | exact resolve eq1517519 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517519
  have eq1517549 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X0 ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1517520 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1517520
    | (have j0 := eq1517520 X0 X1
       grind)
    | exact resolve eq1517520 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517520
  have eq1517574 : ∀ X0 X1 : G, (k (σ (σ X0)) (σ X1)) = (σ (M.op (σ X0) X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (τ (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1517548 X0 X1
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq1517548
    | (have j0 := eq1517548 X0 X1
       grind)
    | exact resolve eq1517548 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517548
  have eq1517575 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X0 ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1517549 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1517549
    | (have j0 := eq1517549 X0 X1
       grind)
    | exact resolve eq1517549 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517549
  have eq1517593 : ∀ X0 X1 : G, (σ (k (σ X0) X1)) = (σ (M.op (σ X0) X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (τ (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1517574 X0 X1
       have i₂ := eq15 (σ X0) X1
       grind)
    | exact superpose eq15 eq1517574
    | (have j0 := eq1517574 X0 X1
       grind)
    | exact resolve eq1517574 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517574
  have eq1517594 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1517575 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1517575
    | (have j0 := eq1517575 X0 X1
       grind)
    | exact resolve eq1517575 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517575
  have eq1517608 : ∀ X0 X1 : G, (σ (k (σ X0) X1)) = (σ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1517593 X0 X1
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq1517593
    | (have j0 := eq1517593 X0 X1
       grind)
    | exact resolve eq1517593 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517593
  have eq1522995 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (M.op X0 X0) = X0 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq1517454 X0 X1
       grind)
    | exact superpose eq1517454 eq10
    | (have j1 := eq1517454 X0 X1
       grind)
    | exact resolve eq10 eq1517454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517454
  have eq1523834 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op X0 X0) = X0 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1522995 X0 X1
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq1522995
    | (have j0 := eq1522995 X0 X1
       grind)
    | exact resolve eq1522995 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522995
  have eq1525214 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op X0 X0) = X0 ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq1523834 X0 (τ X1)
       grind)
    | exact superpose eq1523834 eq35
    | (have j1 := eq1523834 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1523834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1523834
  have eq1526186 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1525214 X0 X1
       have i₂ := eq11119 X1
       grind)
    | exact superpose eq11119 eq1525214
    | (have j0 := eq1525214 X0 X1
       grind)
    | exact resolve eq1525214 eq11119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11119 eq1525214
  have eq1526570 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1526186 X0 X1
       have i₂ := eq11553 X1
       grind)
    | exact superpose eq11553 eq1526186
    | (have j0 := eq1526186 X0 X1
       grind)
    | exact resolve eq1526186 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11553 eq1526186
  have eq1545791 : ∀ X0 X1 : G, (k (σ X0) X1) = (τ (σ (M.op (σ X0) X1))) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (σ X0) X1)
       have i₂ := eq1517608 X0 X1
       grind)
    | exact superpose eq1517608 eq10
    | (have j1 := eq1517608 X0 X1
       grind)
    | exact resolve eq10 eq1517608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517608
  have eq1546668 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1545791 X0 X1
       have i₂ := eq10 (M.op (σ X0) X1)
       grind)
    | exact superpose eq10 eq1545791
    | (have j0 := eq1545791 X0 X1
       grind)
    | exact resolve eq1545791 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545791
  have eq1548233 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1546668 X0 (σ X1)
       grind)
    | exact superpose eq1546668 eq15
    | (have j1 := eq1546668 X0 (σ X1)
       grind)
    | exact resolve eq15 eq1546668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546668
  have eq1548980 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1548233 X0 X1
       have i₂ := eq11809 X1
       grind)
    | exact superpose eq11809 eq1548233
    | (have j0 := eq1548233 X0 X1
       grind)
    | exact resolve eq1548233 eq11809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548233
  have eq1559268 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (τ (k X0 (σ X1))) = (M.op (τ X0) (τ (σ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq332 X1
       have i₂ := eq1526570 X0 (σ X1)
       grind)
    | (have i₁ := eq332 X0
       have i₂ := eq1526570 (M.op (σ X0) (σ X0)) X1
       grind)
    | exact superpose eq1526570 eq332
    | (have j1 := eq1526570 X0 (σ X1)
       grind)
    | exact resolve eq332 eq1526570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq1526570
  have eq1559650 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1559268 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1559268
    | (have j0 := eq1559268 X0 X1
       grind)
    | exact resolve eq1559268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559268
  have eq1559943 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1559650 X0 X1
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq1559650
    | (have j0 := eq1559650 X0 X1
       grind)
    | exact resolve eq1559650 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1559650
  have eq1567134 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ X1 ∨ (k (τ X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1559943 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559943
  have eq1568563 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = (k (τ X0) (M.op (τ X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1567134 X0 (M.op (τ X0) X1)
       have i₂ := eq1012 (τ X0) X1
       grind)
    | exact superpose eq1012 eq1567134
    | (have j0 := eq1567134 X0 (M.op (τ X0) X1)
       grind)
    | (have r₁ := eq1567134 X0 (M.op (τ X0) x)
       have r₂ := eq1012 (τ X0) x
       grind)
    | exact resolve eq1567134 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567134
  have eq1568572 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (k (τ X0) (M.op (τ X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1568563 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568563
  have eq1570116 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1568572 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1568572
    | (have j0 := eq1568572 (σ X0) X1
       grind)
    | exact resolve eq1568572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568572
  have eq1570784 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1570116 X0 X1
       have i₂ := eq11809 X0
       grind)
    | exact superpose eq11809 eq1570116
    | (have j0 := eq1570116 X0 X1
       grind)
    | exact resolve eq1570116 eq11809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11809 eq1570116
  have eq1571560 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq1570784 X0 X1
       grind)
    | exact superpose eq1570784 eq10
    | (have j1 := eq1570784 X0 X1
       grind)
    | exact resolve eq10 eq1570784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570784
  have eq1572455 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1571560 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1571560
    | (have j0 := eq1571560 X0 X1
       grind)
    | exact resolve eq1571560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571560
  have eq2048600 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1548980 x y
       grind)
    | exact superpose eq1548980 eq16
    | (have j1 := eq1548980 x y
       grind)
    | exact resolve eq16 eq1548980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548980
  have eq2051804 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2048600
       have i₂ := eq1517594 x y
       grind)
    | exact superpose eq1517594 eq2048600
    | (have j1 := eq1517594 x x
       grind)
    | (have r₁ := eq2048600
       have r₂ := eq1517594 x y
       grind)
    | exact resolve eq2048600 eq1517594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517594
  have eq2051813 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq2051804
  have eq2051814 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq2051813
  have eq2051917 : (M.op y y) = (τ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2051814
       grind)
    | exact superpose eq2051814 eq10
    | exact resolve eq10 eq2051814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051814
  have eq2052855 : x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2051917
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2051917
    | exact resolve eq2051917 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051917
  have eq2052856 : x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq2052855
  have eq2052877 : ∀ X0 : G, x = (M.op y y) ∨ (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq99 x X0
       have i₂ := eq2052856
       grind)
    | exact superpose eq2052856 eq99
    | exact resolve eq99 eq2052856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2053731 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1923 x x x
       have i₂ := eq2052856
       grind)
    | exact superpose eq2052856 eq1923
    | exact resolve eq1923 eq2052856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052856
  have eq2054228 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq2053731 X0
       have i₂ := eq1012 x X0
       grind)
    | (have i₁ := eq2053731 X0
       have i₂ := eq1012 x (M.op x X0)
       grind)
    | exact superpose eq1012 eq2053731
    | exact resolve eq2053731 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012 eq2053731
  have eq2054944 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq79 y
       have i₂ := eq2054228 X0
       grind)
    | exact superpose eq2054228 eq79
    | (have j1 := eq2054228 X0
       grind)
    | exact resolve eq79 eq2054228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2054994 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq13359 y
       have i₂ := eq2054228 X0
       grind)
    | exact superpose eq2054228 eq13359
    | (have j1 := eq2054228 X0
       grind)
    | exact resolve eq13359 eq2054228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054228
  have eq2060340 : ∀ X0 : G, y = (M.op x y) ∨ (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq79 y
       have i₂ := eq2052877 X0
       grind)
    | exact superpose eq2052877 eq79
    | (have j1 := eq2052877 X0
       grind)
    | exact resolve eq79 eq2052877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2060747 : ∀ X0 : G, y = (M.op (M.op y x) y) ∨ (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq97 y y
       have i₂ := eq2052877 X0
       grind)
    | exact superpose eq2052877 eq97
    | (have j1 := eq2052877 X0
       grind)
    | exact resolve eq97 eq2052877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq2052877
  have eq2095729 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq2054994 X0
       grind)
    | exact superpose eq2054994 eq16
    | (have j1 := eq2054994 X0
       grind)
    | exact resolve eq16 eq2054994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054994
  have eq2097347 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ x = (M.op (M.op x X0) x) ∨ x = (M.op (M.op x X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq2095729 X0
       have i₂ := eq2054944 X1
       grind)
    | exact superpose eq2054944 eq2095729
    | (have j0 := eq2095729 X0
       have j1 := eq2054944 X0
       grind)
    | exact resolve eq2095729 eq2054944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054944 eq2095729
  have eq2097349 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ x = (M.op (M.op x X1) x) := by
    intro X0 X1
    first
    | (have j0 := eq2097347 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097347
  have eq2099406 : ∀ X0 : G, x ≠ x ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq2097349 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097349
  have eq2099407 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq2099406 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099406
  have eq2100508 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x X0) X1) x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op x X0) x
       have i₂ := eq2099407 X0
       grind)
    | exact superpose eq2099407 eq9
    | exact resolve eq9 eq2099407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2101470 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ (M.op (M.op (M.op x X1) x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2100508 y X0
       have i₂ := eq2060340 X1
       grind)
    | exact superpose eq2060340 eq2100508
    | (have j1 := eq2060340 X1
       grind)
    | exact resolve eq2100508 eq2060340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060340 eq2100508
  have eq2103481 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2101470 X0 X1
       have i₂ := eq2099407 X1
       grind)
    | exact superpose eq2099407 eq2101470
    | (have j0 := eq2101470 X0 X1
       grind)
    | exact resolve eq2101470 eq2099407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101470
  have eq2104780 : ∀ X0 : G, x = (M.op y x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq99 y x
       have i₂ := eq2103481 y X0
       grind)
    | exact superpose eq2103481 eq99
    | (have j1 := eq2103481 X0 X0
       grind)
    | exact resolve eq99 eq2103481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq2103481
  have eq2245553 : ∀ X0 : G, y = (M.op (M.op y x) y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2060747 X0
       have i₂ := eq2099407 X0
       grind)
    | exact superpose eq2099407 eq2060747
    | exact resolve eq2060747 eq2099407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060747
  have eq2245558 : ∀ X0 X1 : G, y = (M.op x y) ∨ (M.op x X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2245553 X0
       have i₂ := eq2104780 X1
       grind)
    | exact superpose eq2104780 eq2245553
    | (have j0 := eq2245553 y
       have j1 := eq2104780 y
       grind)
    | exact resolve eq2245553 eq2104780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2104780 eq2245553
  have eq2247565 : ∀ X0 : G, y ≠ y ∨ (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2245558 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245558
  have eq2247566 : ∀ X0 : G, y = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2247565 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247565
  have eq2248569 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq2247566 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247566
  have eq2248570 : y = (M.op x y) := by grind
  clear eq2248569
  have eq2249531 : y = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1572455 x y
       have i₂ := eq2248570
       grind)
    | exact superpose eq2248570 eq1572455
    | (have j0 := eq1572455 x x
       grind)
    | exact resolve eq1572455 eq2248570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572455
  have eq2271623 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2048600
       have i₂ := eq2249531
       grind)
    | exact superpose eq2249531 eq2048600
    | exact resolve eq2048600 eq2249531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048600 eq2249531
  have eq2271889 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq2271623
  have eq2271895 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2271889
       have i₂ := eq2248570
       grind)
    | exact superpose eq2248570 eq2271889
    | exact resolve eq2271889 eq2248570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271889
  have eq2271896 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq2271895
  have eq2281836 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13359 y
       have i₂ := eq2271896
       grind)
    | exact superpose eq2271896 eq13359
    | exact resolve eq13359 eq2271896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13359 eq2271896
  have eq2379340 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq2281836
       grind)
    | exact superpose eq2281836 eq9
    | exact resolve eq9 eq2281836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2281836
  have eq2381110 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2379340 X0
       have i₂ := eq2099407 X0
       grind)
    | exact superpose eq2099407 eq2379340
    | exact resolve eq2379340 eq2099407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099407 eq2379340
  have eq2384688 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq2381110 X0
       grind)
    | exact superpose eq2381110 eq16
    | (have j1 := eq2381110 X0
       grind)
    | exact resolve eq16 eq2381110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2381110
  have eq2386248 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2384688 X0
       have i₂ := eq2248570
       grind)
    | exact superpose eq2248570 eq2384688
    | (have j0 := eq2384688 X0
       grind)
    | exact resolve eq2384688 eq2248570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384688
  have eq2386249 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2386248 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2386248
  have eq2386446 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13361 x X0
       have i₂ := eq2386249 x
       grind)
    | exact superpose eq2386249 eq13361
    | exact resolve eq13361 eq2386249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13361
  have eq2387255 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1923 x X1 X0
       have i₂ := eq2386249 X0
       grind)
    | exact superpose eq2386249 eq1923
    | exact resolve eq1923 eq2386249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923
  have eq2390200 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2387255 X0 X0
       have i₂ := eq2386249 X0
       grind)
    | exact superpose eq2386249 eq2387255
    | exact resolve eq2387255 eq2386249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2386249 eq2387255
  have eq2733576 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2386446 X0
       have i₂ := eq2390200 X0 (σ x)
       grind)
    | exact superpose eq2390200 eq2386446
    | exact resolve eq2386446 eq2390200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2386446 eq2390200
  have eq2734104 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2733576 (σ y)
       grind)
    | exact superpose eq2733576 eq16
    | exact resolve eq16 eq2733576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2733576
  have eq2738462 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2734104
       have i₂ := eq2248570
       grind)
    | exact superpose eq2248570 eq2734104
    | exact resolve eq2734104 eq2248570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248570 eq2734104
  have eq2738463 : False := by grind
  exact eq2738463

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq62 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X4) X3) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) X5)) X1) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X0 X5
       have i₂ := eq25 X3 X2 X4 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25
  have eq99 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq9
    | exact resolve eq9 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq16
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq16 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq346 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (k (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq62 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq62 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq62 X0 (τ X0)
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq355 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq354 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq356 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (k (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq346 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq357 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq356 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq359 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq355 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq355
    | (have j0 := eq355 X0
       grind)
    | exact resolve eq355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq994 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq86 X0 X1 X2 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq86
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1012 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq994 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq994
    | exact resolve eq994 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1884 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) (M.op X0 X4)) (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq95 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X1 X0 X2 X4
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq95
    | exact resolve eq95 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1923 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op X0 X3) (M.op X0 X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1884 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq1884
    | exact resolve eq1884 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884
  have eq3436 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq10
    | (have j1 := eq359 X0
       grind)
    | exact resolve eq10 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq7278 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq357 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq357
    | exact resolve eq357 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq7357 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7278 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7278
    | (have j0 := eq7278 X0 X1
       grind)
    | exact resolve eq7278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7278
  have eq11164 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq3436
  have eq11244 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11164 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq11164
    | (have j0 := eq11164 X0
       grind)
    | exact resolve eq11164 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq11164
  have eq11245 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq11244 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11244
  have eq11273 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq11245 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11245
    | exact resolve eq11245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11245
  have eq11388 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq11273 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq11273
    | exact resolve eq11273 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11273
  have eq11397 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq11388 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11388
    | exact resolve eq11388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11388
  have eq12168 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq11397 (σ X0)
       grind)
    | exact superpose eq11397 eq15
    | exact resolve eq15 eq11397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12220 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12168 X0
       have i₂ := eq11397 X0
       grind)
    | exact superpose eq11397 eq12168
    | exact resolve eq12168 eq11397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11397 eq12168
  have eq13701 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq79 (σ X0)
       have i₂ := eq12220 X0
       grind)
    | exact superpose eq12220 eq79
    | exact resolve eq79 eq12220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13703 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99 (σ X0) X1
       have i₂ := eq12220 X0
       grind)
    | exact superpose eq12220 eq99
    | exact resolve eq99 eq12220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81165 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq7357 (τ X0) X1
       grind)
    | exact superpose eq7357 eq18
    | (have j1 := eq7357 (τ X0) X1
       grind)
    | exact resolve eq18 eq7357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7357
  have eq81358 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ (k (τ X0) X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81165 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81165
    | (have j0 := eq81165 X0 X1
       grind)
    | exact resolve eq81165 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81165
  have eq81494 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81358 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq81358
    | (have j0 := eq81358 X0 X1
       grind)
    | exact resolve eq81358 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq81358
  have eq956514 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81494 (σ X0) X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq81494
    | (have j0 := eq81494 (σ X0) X1
       grind)
    | exact resolve eq81494 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81494
  have eq957379 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq956514 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq956514
    | (have j0 := eq956514 X0 X1
       grind)
    | exact resolve eq956514 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956514
  have eq957677 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq957379 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq957379
    | (have j0 := eq957379 X0 X1
       grind)
    | exact resolve eq957379 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957379
  have eq960584 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq957677 x y
       grind)
    | exact superpose eq957677 eq110
    | (have j1 := eq957677 x y
       grind)
    | (have r₁ := eq110
       have r₂ := eq957677 x y
       grind)
    | exact resolve eq110 eq957677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq957677
  have eq961038 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq960584
  have eq961097 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq120 x y
       grind)
    | (have r₁ := eq961038
       have r₂ := eq120 x y
       grind)
    | exact resolve eq961038 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq961038
  have eq961272 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq961097
       have i₂ := eq12220 y
       grind)
    | exact superpose eq12220 eq961097
    | exact resolve eq961097 eq12220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961097
  have eq965520 : (M.op y y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq961272
       grind)
    | exact superpose eq961272 eq10
    | exact resolve eq10 eq961272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961272
  have eq966026 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq965520
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq965520
    | exact resolve eq965520 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965520
  have eq966027 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq966026
  have eq967709 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1012 (σ x) (σ y)
       have i₂ := eq966027
       grind)
    | exact superpose eq966027 eq1012
    | exact resolve eq1012 eq966027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966027
  have eq968444 : (σ x) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq967709
       have i₂ := eq12220 x
       grind)
    | exact superpose eq12220 eq967709
    | exact resolve eq967709 eq12220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12220 eq967709
  have eq970422 : (M.op x x) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq968444
       grind)
    | exact superpose eq968444 eq10
    | exact resolve eq10 eq968444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968444
  have eq970931 : x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq970422
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq970422
    | exact resolve eq970422 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970422
  have eq970982 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq79 y
       have i₂ := eq970931
       grind)
    | exact superpose eq970931 eq79
    | exact resolve eq79 eq970931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq971020 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13701 y
       have i₂ := eq970931
       grind)
    | exact superpose eq970931 eq13701
    | exact resolve eq13701 eq970931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13701 eq970931
  have eq983834 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq971020
       grind)
    | exact superpose eq971020 eq16
    | exact resolve eq16 eq971020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971020
  have eq986470 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq983834
       have i₂ := eq970982
       grind)
    | exact superpose eq970982 eq983834
    | exact resolve eq983834 eq970982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970982 eq983834
  have eq986472 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by grind
  clear eq986470
  have eq986473 : x = (M.op x x) := by grind
  clear eq986472
  have eq986480 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq99 x X0
       have i₂ := eq986473
       grind)
    | exact superpose eq986473 eq99
    | exact resolve eq99 eq986473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq986516 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13703 x X0
       have i₂ := eq986473
       grind)
    | exact superpose eq986473 eq13703
    | exact resolve eq13703 eq986473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13703
  have eq987221 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq1923 x x x
       have i₂ := eq986473
       grind)
    | exact superpose eq986473 eq1923
    | exact resolve eq1923 eq986473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986473
  have eq987351 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq987221 X0
       have i₂ := eq1012 x X0
       grind)
    | (have i₁ := eq987221 X0
       have i₂ := eq1012 x (M.op x X0)
       grind)
    | exact superpose eq1012 eq987221
    | exact resolve eq987221 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012 eq987221
  have eq992669 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq986480 X0
       have i₂ := eq987351 X0
       grind)
    | exact superpose eq987351 eq986480
    | exact resolve eq986480 eq987351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986480 eq987351
  have eq993430 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1923 x X1 X0
       have i₂ := eq992669 X0
       grind)
    | exact superpose eq992669 eq1923
    | exact resolve eq1923 eq992669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923
  have eq995154 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq993430 X0 X0
       have i₂ := eq992669 X0
       grind)
    | exact superpose eq992669 eq993430
    | exact resolve eq993430 eq992669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993430
  have eq1298162 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq986516 X0
       have i₂ := eq995154 X0 (σ x)
       grind)
    | exact superpose eq995154 eq986516
    | exact resolve eq986516 eq995154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986516 eq995154
  have eq1298505 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1298162 (σ y)
       grind)
    | exact superpose eq1298162 eq16
    | exact resolve eq16 eq1298162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298162
  have eq1301595 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1298505
       have i₂ := eq992669 y
       grind)
    | exact superpose eq992669 eq1298505
    | exact resolve eq1298505 eq992669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992669 eq1298505
  have eq1301596 : False := by grind
  exact eq1301596

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  clear eq36
  have eq51 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq99 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq110 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq99
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq114
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq209 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq216 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq515 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq515 (M.op X0 X1)
       grind)
    | exact superpose eq515 eq53
    | exact resolve eq53 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq522 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq515 X0
       grind)
    | exact superpose eq515 eq14
    | exact resolve eq14 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq543 : y = (M.op (M.op y (M.op x y)) y) := by
    first
    | (have i₁ := eq519 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq519
    | (have j0 := eq519 x y
       grind)
    | exact resolve eq519 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq705 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq873 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq522
    | exact resolve eq522 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq875 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq522
    | exact resolve eq522 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq522
  have eq9728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq9728
    | exact resolve eq9728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9728
  have eq9740 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq9729
       have r₂ := eq28
       grind)
    | exact resolve eq9729 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9729
  have eq9742 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq9740
    | exact resolve eq9740 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9740
  have eq9747 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq9742
  have eq9769 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq9747
    | exact resolve eq9747 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9747
  have eq11562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq9769 eq115
    | exact resolve eq115 eq9769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq9769
  have eq11573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11562
  have eq11576 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11573
       have r₂ := eq28
       grind)
    | exact resolve eq11573 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11573
  have eq12182 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11576
  have eq12218 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12182
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12182
    | exact resolve eq12182 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12182
  have eq12303 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq12218
       grind)
    | exact superpose eq12218 eq45
    | exact resolve eq45 eq12218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq12218
  have eq12321 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq12303
    | exact resolve eq12303 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12303
  have eq12482 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12321 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12482
    | exact resolve eq12482 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12482
  have eq12496 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12485
       have r₂ := eq28
       grind)
    | exact resolve eq12485 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12485
  have eq12498 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12496
    | exact resolve eq12496 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12496
  have eq12499 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12498
  have eq12507 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12499
  have eq12543 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12507
    | exact resolve eq12507 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12507
  have eq12602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12543 eq12321
    | exact resolve eq12321 eq12543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12321 eq12543
  have eq12606 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12602
  have eq12612 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12606
       have r₂ := eq28
       grind)
    | exact resolve eq12606 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12606
  have eq12620 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12612 eq216
    | exact resolve eq216 eq12612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq12643 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12612 eq875
    | exact resolve eq875 eq12612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq12686 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq12790 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12643 eq12620
    | exact resolve eq12620 eq12643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12620 eq12643
  have eq12832 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12790
  have eq12835 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12832
    | exact resolve eq12832 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12832
  have eq12870 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12835 eq12612
    | exact resolve eq12612 eq12835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12612 eq12835
  have eq12873 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq12870
  have eq12881 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12873 eq30
    | exact resolve eq30 eq12873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12873
  have eq13053 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq12881
    | exact resolve eq12881 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12881
  have eq13102 : y = (M.op (M.op x x) y) ∨ x = y := by
    first
    | exact superpose eq13053 eq209
    | exact resolve eq209 eq13053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq13131 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq13053 eq873
    | exact resolve eq873 eq13053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20910 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq13102
       have i₂ := eq13131
       grind)
    | exact superpose eq13131 eq13102
    | exact resolve eq13102 eq13131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13102 eq13131
  have eq20948 : y = (M.op x y) ∨ x = y := by grind
  clear eq20910
  have eq20950 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq20948
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20948
    | exact resolve eq20948 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20948
  have eq21036 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq20950 eq13053
    | exact resolve eq13053 eq20950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13053 eq20950
  have eq21039 : x = y := by grind
  clear eq21036
  have eq21102 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq21039
       grind)
    | exact superpose eq21039 eq19
    | exact resolve eq19 eq21039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq21103 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq21039
       grind)
    | exact superpose eq21039 eq25
    | exact resolve eq25 eq21039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq21163 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq543
       have i₂ := eq21039
       grind)
    | exact superpose eq21039 eq543
    | exact resolve eq543 eq21039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq21039
  have eq21183 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq873 eq21163
    | exact resolve eq21163 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq21163
  have eq21234 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq21103
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21103
    | exact resolve eq21103 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21103
  have eq21235 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21234 eq27
    | exact resolve eq27 eq21234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq21234
  have eq21430 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq21102
       grind)
    | exact superpose eq21102 eq110
    | exact resolve eq110 eq21102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq21453 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  clear eq21102
  have eq21496 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq21430
    | exact resolve eq21430 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21430
  have eq21892 : x = (k (M.op x y) x) := by
    first
    | exact superpose eq21183 eq21453
    | exact resolve eq21453 eq21183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21183 eq21453
  have eq23399 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21496 eq12686
    | exact resolve eq12686 eq21496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12686 eq21496
  have eq23422 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq23399
  have eq23426 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21235 eq23422
    | exact resolve eq23422 eq21235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23422
  have eq23437 : x = (M.op x y) := by
    first
    | (have r₁ := eq23426
       have r₂ := eq28
       grind)
    | exact resolve eq23426 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23426
  have eq23445 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq23437 eq21
    | exact resolve eq21 eq23437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq23534 : x = (k x x) := by
    first
    | exact superpose eq23437 eq21892
    | exact resolve eq21892 eq23437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21892 eq23437
  have eq23611 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23445
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23445
    | exact resolve eq23445 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23445
  have eq23952 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq705 x x
       have i₂ := eq23534
       grind)
    | exact superpose eq23534 eq705
    | (have j0 := eq705 x x
       grind)
    | exact resolve eq705 eq23534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq23534
  have eq23953 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq23952
  have eq23954 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq23953
  have eq23967 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq23954
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23954
    | exact resolve eq23954 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq23954
  have eq23988 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21235 eq23967
    | exact resolve eq23967 eq21235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21235 eq23967
  have eq24004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23611 eq23988
    | exact resolve eq23988 eq23611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23611 eq23988
  have eq24020 : False := by grind
  exact eq24020

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_y_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
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
  clear eq36
  have eq47 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq76 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq83
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq94
    | exact resolve eq94 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq108 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq120 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) ∨ (M.op x x) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq11 sF0 x
       grind)
    | exact superpose eq11 eq108
    | (have j1 := eq11 (M.op x y) x
       grind)
    | exact resolve eq108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ y)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq432 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq438 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq432 X0
       grind)
    | exact superpose eq432 eq14
    | exact resolve eq14 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq950 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq438 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq438
    | exact resolve eq438 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq953 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq438
    | exact resolve eq438 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51 eq438
    | exact resolve eq438 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq438
  have eq1044 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op x X0)
       have i₂ := eq950 x X0
       grind)
    | exact superpose eq950 eq50
    | exact resolve eq50 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq10708 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq86 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq86
    | (have j0 := eq86 x
       grind)
    | exact resolve eq86 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq10760 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq10708
    | exact resolve eq10708 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10708
  have eq10776 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10760
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq10760
    | exact resolve eq10760 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10760
  have eq10780 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq10776
    | exact resolve eq10776 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10776
  have eq19495 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19495
    | exact resolve eq19495 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19495
  have eq19507 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq19496
       have r₂ := eq28
       grind)
    | exact resolve eq19496 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19496
  have eq19509 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19507
    | exact resolve eq19507 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19507
  have eq19535 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq19509
  have eq19875 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  have eq19909 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19535 eq950
    | exact resolve eq950 eq19535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19535
  have eq19916 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19909
    | exact resolve eq19909 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19909
  have eq19966 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19916 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq11 eq19916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19916
  have eq19967 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq955 eq19966
    | exact resolve eq19966 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19966
  have eq19969 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq955 eq19967
    | exact resolve eq19967 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19967
  have eq19970 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq19969
  have eq20132 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19970 eq77
    | (have r₁ := eq77
       have r₂ := eq19970
       grind)
    | exact resolve eq77 eq19970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19970
  have eq20195 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq20132
  have eq20196 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq20195
  have eq20284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20196 eq96
    | exact resolve eq96 eq20196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20196
  have eq20292 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20284
  have eq20294 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20292
       have r₂ := eq28
       grind)
    | exact resolve eq20292 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20292
  have eq20297 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq20294
       grind)
    | exact superpose eq20294 eq76
    | (have r₁ := eq76
       have r₂ := eq20294
       grind)
    | exact resolve eq76 eq20294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20359 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20294
  have eq20361 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20297
  have eq22744 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20361
       have r₂ := eq20359
       grind)
    | exact resolve eq20361 eq20359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20359 eq20361
  have eq22746 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83
       have i₂ := eq22744
       grind)
    | exact superpose eq22744 eq83
    | exact resolve eq83 eq22744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22744
  have eq22766 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq22746
    | exact resolve eq22746 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22746
  have eq22779 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22766 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq22766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22782 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq22779
    | exact resolve eq22779 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22779
  have eq22793 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22782
       have r₂ := eq28
       grind)
    | exact resolve eq22782 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22782
  have eq22795 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq22793
    | exact resolve eq22793 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22793
  have eq33685 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22795
  have eq35390 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33685 eq950
    | exact resolve eq950 eq33685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33685
  have eq35411 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq35390
    | exact resolve eq35390 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35390
  have eq35412 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35411
  have eq35416 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35412 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq11 eq35412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35412
  have eq35417 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq955 eq35416
    | exact resolve eq35416 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35416
  have eq35418 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq35417
  have eq35421 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq955 eq35418
    | exact resolve eq35418 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35418
  have eq35422 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq35421
  have eq35428 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq35422 eq77
    | (have r₁ := eq77
       have r₂ := eq35422
       grind)
    | exact resolve eq77 eq35422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35422
  have eq35509 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq35428
  have eq35510 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq35509
  have eq37690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq35510 eq22766
    | exact resolve eq22766 eq35510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22766 eq35510
  have eq37696 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq37690
  have eq37711 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq37696
       have r₂ := eq28
       grind)
    | exact resolve eq37696 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37696
  have eq37751 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq37711
  have eq38417 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83
       have i₂ := eq37751
       grind)
    | exact superpose eq37751 eq83
    | exact resolve eq83 eq37751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37751
  have eq38456 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38417
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38417
    | exact resolve eq38417 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38417
  have eq38528 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38456 eq10780
    | exact resolve eq10780 eq38456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38552 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq38528
  have eq44692 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq38552
  have eq45367 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44692 eq950
    | exact resolve eq950 eq44692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44692
  have eq45393 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq45367
    | exact resolve eq45367 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45367
  have eq45394 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq45393
  have eq45398 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45394 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq11 eq45394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45394
  have eq45399 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq955 eq45398
    | exact resolve eq45398 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45398
  have eq45400 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq45399
  have eq45403 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq955 eq45400
    | exact resolve eq45400 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45400
  have eq45404 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq45403
  have eq45411 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45404 eq77
    | (have r₁ := eq77
       have r₂ := eq45404
       grind)
    | exact resolve eq77 eq45404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq45404
  have eq45498 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45411
  have eq45499 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45498
  have eq46498 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45499 eq38456
    | exact resolve eq38456 eq45499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38456 eq45499
  have eq46500 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq46498
  have eq46522 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46500 eq28
    | exact resolve eq28 eq46500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46561 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46500 eq19875
    | exact resolve eq19875 eq46500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19875
  have eq46565 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq46561
  have eq62607 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46565 eq96
    | exact resolve eq96 eq46565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq46565
  have eq62643 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq62607
  have eq62702 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq62643
  have eq62859 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq950 x x
       have i₂ := eq62702
       grind)
    | exact superpose eq62702 eq950
    | exact resolve eq950 eq62702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950 eq62702
  have eq62895 : x = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62859
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq62859
    | exact resolve eq62859 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62859
  have eq62899 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62895 eq108
    | exact resolve eq108 eq62895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq62895
  have eq62930 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62899
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq62899
    | exact resolve eq62899 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62899
  have eq118005 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x x) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq953 eq120
    | exact resolve eq120 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq118006 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x x) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq118005
    | exact resolve eq118005 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118005
  have eq118007 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq953 eq118006
    | exact resolve eq118006 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118006
  have eq118008 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq118007
  have eq118594 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq118008 eq62930
    | exact resolve eq62930 eq118008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62930 eq118008
  have eq118616 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq118594
  have eq118639 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq118616
       grind)
    | exact superpose eq118616 eq76
    | (have r₁ := eq76
       have r₂ := eq118616
       grind)
    | exact resolve eq76 eq118616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq118616
  have eq118767 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq118639
  have eq118768 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq118767
  have eq118793 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq118768
       grind)
    | exact superpose eq118768 eq83
    | exact resolve eq83 eq118768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq118768
  have eq118868 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq118793
    | exact resolve eq118793 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118793
  have eq119021 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq118868 eq10780
    | exact resolve eq10780 eq118868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10780
  have eq119084 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq119021
       have r₂ := eq28
       grind)
    | exact resolve eq119021 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119021
  have eq148288 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq119084
  have eq148309 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq148288
       have r₂ := eq46500
       grind)
    | exact resolve eq148288 eq46500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46500 eq148288
  have eq148376 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq148309
  have eq148524 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq148376 eq118868
    | exact resolve eq118868 eq148376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118868 eq148376
  have eq148530 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq148524
  have eq148615 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq148530 eq955
    | exact resolve eq955 eq148530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148530
  have eq148945 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq148615
  have eq149318 : (τ (σ x)) = (k x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq148945 eq56
    | exact resolve eq56 eq148945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq148945
  have eq149401 : x = (k x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq149318
    | exact resolve eq149318 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149318
  have eq149577 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq78 x
       have i₂ := eq149401
       grind)
    | exact superpose eq149401 eq78
    | (have j0 := eq78 x
       grind)
    | exact resolve eq78 eq149401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq149401
  have eq149578 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq149577
  have eq149677 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq149578
       grind)
    | exact superpose eq149578 eq47
    | exact resolve eq47 eq149578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149702 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1044 x
       have i₂ := eq149578
       grind)
    | exact superpose eq149578 eq1044
    | exact resolve eq1044 eq149578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq149578
  have eq149850 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq953 eq149702
    | exact resolve eq149702 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149702
  have eq155893 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq149850 eq149677
    | exact resolve eq149677 eq149850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149677 eq149850
  have eq155955 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq155893
  have eq155956 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq155955
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq155955
    | exact resolve eq155955 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155955
  have eq155957 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq155956
  have eq155959 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq155957 eq29
    | exact resolve eq29 eq155957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq155957
  have eq156576 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq155959
    | exact resolve eq155959 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq155959
  have eq156577 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq156576 eq21
    | exact resolve eq21 eq156576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156576
  have eq157028 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq156577
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq156577
    | exact resolve eq156577 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156577
  have eq157181 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq157028 eq46522
    | (have r₁ := eq46522
       have r₂ := eq157028
       grind)
    | exact resolve eq46522 eq157028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157297 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq157181
  have eq157403 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq157297 eq202
    | exact resolve eq202 eq157297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq157428 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq157297 eq955
    | exact resolve eq955 eq157297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq157297
  have eq162036 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq157428 eq157403
    | exact resolve eq157403 eq157428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157403 eq157428
  have eq162107 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq162036
  have eq162117 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq162107
    | exact resolve eq162107 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq162107
  have eq162123 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq162117 eq28
    | exact resolve eq28 eq162117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162117
  have eq162248 : x = (M.op x y) := by
    first
    | (have r₁ := eq162123
       have r₂ := eq157028
       grind)
    | exact resolve eq162123 eq157028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157028 eq162123
  have eq162252 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq162248 eq21
    | exact resolve eq21 eq162248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq162347 : x = (M.op x x) := by
    first
    | exact superpose eq162248 eq953
    | exact resolve eq953 eq162248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq162770 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq162252
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq162252
    | exact resolve eq162252 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162252
  have eq163540 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq162347
       grind)
    | exact superpose eq162347 eq47
    | exact resolve eq47 eq162347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq163718 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq162248 eq163540
    | exact resolve eq163540 eq162248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163540
  have eq163751 : y = (M.op x y) := by
    first
    | (have i₁ := eq163718
       have i₂ := eq162347
       grind)
    | exact superpose eq162347 eq163718
    | exact resolve eq163718 eq162347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162347 eq163718
  have eq163760 : y = (M.op x y) := by
    first
    | (have i₁ := eq163751
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq163751
    | exact resolve eq163751 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq163751
  have eq163762 : x = y := by
    first
    | exact superpose eq162248 eq163760
    | exact resolve eq163760 eq162248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162248 eq163760
  have eq163767 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq163762
       grind)
    | exact superpose eq163762 eq25
    | exact resolve eq25 eq163762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq163762
  have eq164260 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq163767
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq163767
    | exact resolve eq163767 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq163767
  have eq164421 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq162770 eq164260
    | exact resolve eq164260 eq162770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164260
  have eq164639 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq164421 eq46522
    | (have r₁ := eq46522
       have r₂ := eq164421
       grind)
    | exact resolve eq46522 eq164421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46522 eq164421
  have eq164755 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq164639
  have eq164835 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq162770 eq164755
    | exact resolve eq164755 eq162770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162770 eq164755
  have eq165024 : False := by grind
  exact eq165024

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq28 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq39 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq28
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  have eq57 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq62 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq54 X1 x x X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq68 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 (M.op X1 X0)
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq68
    | exact resolve eq68 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq99 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq110 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ X1 = X2 ∨ (k X2 X1) = X2 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq119 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X2 X1) = X2 ∨ (M.op X1 X1) = X0 ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq110 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq137 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X2) (M.op X1 X0)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X2) X1 X0
       have i₂ := eq81 X2 X1
       grind)
    | exact superpose eq81 eq9
    | exact resolve eq9 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq119 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq263 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq262 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq262
    | (have j0 := eq262 (σ X0)
       grind)
    | exact resolve eq262 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq262 (τ X0)
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq262
    | (have j0 := eq262 (τ X0)
       grind)
    | exact resolve eq262 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq288 : ∀ X0 X1 : G, (σ (k (k (τ (M.op (σ X1) (σ X1))) X1) X0)) = (k (M.op (M.op (σ X1) (σ X1)) (σ X1)) (σ X0)) := by
    intro X0 X1
    grind
  clear eq22
  have eq303 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (k (k (τ (M.op (σ X1) (σ X1))) X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 X1
       have i₂ := eq62 (σ X1)
       grind)
    | (have i₁ := eq288 X0 X1
       have i₂ := eq62 (M.op (M.op (σ X1) (σ X1)) (σ X1))
       grind)
    | exact superpose eq62 eq288
    | exact resolve eq288 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq305 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (k (k (τ (M.op (σ X1) (σ X1))) X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq303
    | exact resolve eq303 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq402 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq99
  have eq886 : ∀ X0 X1 : G, (k (k (τ (M.op (σ X1) (σ X1))) X1) X0) = (τ (σ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (k (τ (M.op (σ X1) (σ X1))) X1) X0)
       have i₂ := eq305 X0 X1
       grind)
    | exact superpose eq305 eq10
    | exact resolve eq10 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq920 : ∀ X0 X1 : G, (k X1 X0) = (k (k (τ (M.op (σ X1) (σ X1))) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq886 X0 X1
       have i₂ := eq10 (k X1 X0)
       grind)
    | exact superpose eq10 eq886
    | exact resolve eq886 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq956 : ∀ X0 X1 : G, (τ (k (σ X1) X0)) = (k (k (τ (τ (M.op (σ (σ X1)) (σ (σ X1))))) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (τ (M.op (σ (σ X1)) (σ (σ X1)))) X1 X0
       have i₂ := eq920 X0 (σ X1)
       grind)
    | exact superpose eq920 eq39
    | exact resolve eq39 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq920
  have eq975 : ∀ X0 X1 : G, (k X1 (τ X0)) = (k (k (τ (τ (M.op (σ (σ X1)) (σ (σ X1))))) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq956
    | exact resolve eq956 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq956
  have eq1925 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq62 (τ X0)
       grind)
    | exact superpose eq62 eq56
    | exact resolve eq56 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1926 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1925 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1925
    | exact resolve eq1925 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925
  have eq1982 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq1926 (τ X0)
       grind)
    | exact superpose eq1926 eq19
    | exact resolve eq19 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926
  have eq1986 : ∀ X0 : G, (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1982 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1982
    | exact resolve eq1982 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982
  have eq2287 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq57
    | exact resolve eq57 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq62
  have eq2288 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2287 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2287
    | exact resolve eq2287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2287
  have eq2322 : ∀ X0 : G, (τ (σ X0)) = (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (τ (M.op (σ (σ X0)) (σ (σ X0)))) X0
       have i₂ := eq2288 (σ X0)
       grind)
    | exact superpose eq2288 eq23
    | exact resolve eq23 eq2288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2288
  have eq2327 : ∀ X0 : G, (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2322 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2322
    | exact resolve eq2322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2322
  have eq2427 : ∀ X0 : G, (k (τ (τ (σ (k (σ X0) (σ X0))))) X0) = X0 ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2327 X0
       have i₂ := eq263 (σ X0)
       grind)
    | exact superpose eq263 eq2327
    | (have j1 := eq263 (σ X0)
       grind)
    | exact resolve eq2327 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq2327
  have eq2458 : ∀ X0 : G, (k (τ (k (σ X0) (σ X0))) X0) = X0 ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2427 X0
       have i₂ := eq10 (k (σ X0) (σ X0))
       grind)
    | exact superpose eq10 eq2427
    | (have j0 := eq2427 X0
       grind)
    | exact resolve eq2427 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2427
  have eq2464 : ∀ X0 : G, (k (k (τ (σ X0)) X0) X0) = X0 ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2458 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq2458
    | (have j0 := eq2458 X0
       grind)
    | exact resolve eq2458 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2458
  have eq2467 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2464 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2464
    | (have j0 := eq2464 X0
       grind)
    | exact resolve eq2464 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2464
  have eq3139 : ∀ X0 : G, (k (σ (σ (τ (k (τ X0) (τ X0))))) X0) = X0 ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1986 X0
       have i₂ := eq264 (τ X0)
       grind)
    | exact superpose eq264 eq1986
    | (have j1 := eq264 (τ X0)
       grind)
    | exact resolve eq1986 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq3172 : ∀ X0 : G, (k (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3139 X0
       have i₂ := eq11 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq11 eq3139
    | (have j0 := eq3139 X0
       grind)
    | exact resolve eq3139 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3139
  have eq3178 : ∀ X0 : G, (k (k (σ (τ X0)) X0) X0) = X0 ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3172 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq3172
    | (have j0 := eq3172 X0
       grind)
    | exact resolve eq3172 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3172
  have eq3183 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3178 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3178
    | (have j0 := eq3178 X0
       grind)
    | exact resolve eq3178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178
  have eq3449 : ∀ X0 : G, (k (σ (σ (τ (τ X0)))) X0) = X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1986 X0
       have i₂ := eq3183 X0
       grind)
    | exact superpose eq3183 eq1986
    | (have j1 := eq3183 X0
       grind)
    | exact resolve eq1986 eq3183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986 eq3183
  have eq3491 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3449 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq3449
    | (have j0 := eq3449 X0
       grind)
    | exact resolve eq3449 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3449
  have eq3504 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3491 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3491
    | (have j0 := eq3491 X0
       grind)
    | exact resolve eq3491 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3491
  have eq3532 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq121 X1 X0 (k X0 X0)
       have i₂ := eq3504 X0
       grind)
    | exact superpose eq3504 eq121
    | (have j0 := eq121 X1 X0 X0
       have j1 := eq3504 X0
       grind)
    | exact resolve eq121 eq3504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq3504
  have eq3537 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3532 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3532
  have eq18588 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k (k (τ (τ (σ (σ X0)))) X0) (τ X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq975 X1 X0
       have i₂ := eq2467 X0
       grind)
    | exact superpose eq2467 eq975
    | (have j1 := eq2467 X0
       grind)
    | exact resolve eq975 eq2467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975 eq2467
  have eq18613 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k (k (τ (σ X0)) X0) (τ X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18588 X0 X1
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq18588
    | (have j0 := eq18588 X0 X1
       grind)
    | exact resolve eq18588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18588
  have eq18624 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k (k X0 X0) (τ X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18613 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18613
    | (have j0 := eq18613 X0 X1
       grind)
    | exact resolve eq18613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18613
  have eq18787 : ∀ X0 : G, (τ X0) ≠ (k (τ X0) (τ X0)) ∨ (τ X0) = (k (k (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq18624 (τ X0) x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18624
  have eq18800 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (k (k (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18787 X0
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq18787
    | (have j0 := eq18787 X0
       grind)
    | exact resolve eq18787 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18787
  have eq18832 : ∀ X0 : G, (τ X0) = (k (τ (k X0 X0)) (τ X0)) ∨ (τ X0) ≠ (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18800 X0
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq18800
    | (have j0 := eq18800 X0
       grind)
    | exact resolve eq18800 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18800
  have eq18836 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq18832 X0
       have i₂ := eq30 X0 (k X0 X0)
       grind)
    | exact superpose eq30 eq18832
    | (have j0 := eq18832 X0
       grind)
    | exact resolve eq18832 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18832
  have eq19293 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18836 X0
       have i₂ := eq3537 X0 X1
       grind)
    | exact superpose eq3537 eq18836
    | (have j1 := eq3537 X0 X1
       grind)
    | exact resolve eq18836 eq3537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3537 eq18836
  have eq19331 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq19293 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19293
  have eq20193 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq118 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq118
    | (have j0 := eq118 X0 X1
       grind)
    | exact resolve eq118 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq20686 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20193 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq20193
    | (have j0 := eq20193 X0 X1
       grind)
    | exact resolve eq20193 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20193
  have eq23888 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq402 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq23890 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23888 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23888
  have eq23891 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23890 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23890
  have eq24135 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23891 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq23891
    | exact resolve eq23891 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24329 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24135 X0
       have i₂ := eq23891 X0
       grind)
    | exact superpose eq23891 eq24135
    | exact resolve eq24135 eq23891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24135
  have eq24566 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq24329 X0
       grind)
    | exact superpose eq24329 eq9
    | exact resolve eq9 eq24329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24577 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq81 (σ X0) (σ X0)
       have i₂ := eq24329 X0
       grind)
    | exact superpose eq24329 eq81
    | exact resolve eq81 eq24329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43854 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19331 X0 X1
       have i₂ := eq23891 X0
       grind)
    | exact superpose eq23891 eq19331
    | (have j0 := eq19331 X0 X1
       grind)
    | exact resolve eq19331 eq23891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19331 eq23891
  have eq44383 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43854 (σ X0) X1
       have i₂ := eq24329 X0
       grind)
    | exact superpose eq24329 eq43854
    | (have j0 := eq43854 (σ X0) X1
       grind)
    | exact resolve eq43854 eq24329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24329 eq43854
  have eq44849 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44383 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq44383
    | (have j0 := eq44383 X0 X1
       grind)
    | exact resolve eq44383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44383
  have eq44859 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44849 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44849
    | (have j0 := eq44849 X0 X1
       grind)
    | exact resolve eq44849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44849
  have eq71303 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq44859 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq44859 X0 (σ X0)
       grind)
    | exact superpose eq44859 eq10
    | (have j1 := eq44859 X0 X1
       grind)
    | exact resolve eq10 eq44859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44859
  have eq72751 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71303 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71303
    | (have j0 := eq71303 X1 (σ X0)
       grind)
    | exact resolve eq71303 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71303
  have eq74041 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72751 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq72751
    | (have j0 := eq72751 X0 X1
       grind)
    | exact resolve eq72751 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72751
  have eq76326 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74041 y x
       grind)
    | exact superpose eq74041 eq16
    | (have j1 := eq74041 y x
       grind)
    | exact resolve eq16 eq74041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74041
  have eq77432 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq76326
       have i₂ := eq20686 y x
       grind)
    | exact superpose eq20686 eq76326
    | (have j1 := eq20686 y x
       grind)
    | (have r₁ := eq76326
       have r₂ := eq20686 y x
       grind)
    | exact resolve eq76326 eq20686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20686 eq76326
  have eq77433 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq77432
  have eq77434 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq77433
  have eq77523 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24577 x
       have i₂ := eq77434
       grind)
    | exact superpose eq77434 eq24577
    | exact resolve eq24577 eq77434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24577
  have eq77607 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq81 x x
       have i₂ := eq77434
       grind)
    | exact superpose eq77434 eq81
    | exact resolve eq81 eq77434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77434
  have eq85266 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77523
       grind)
    | exact superpose eq77523 eq16
    | exact resolve eq16 eq77523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77523
  have eq85396 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85266
       have i₂ := eq77607
       grind)
    | exact superpose eq77607 eq85266
    | exact resolve eq85266 eq77607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77607 eq85266
  have eq85399 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by grind
  clear eq85396
  have eq85400 : x = (M.op x x) := by grind
  clear eq85399
  have eq85462 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24566 x X0
       have i₂ := eq85400
       grind)
    | exact superpose eq85400 eq24566
    | exact resolve eq24566 eq85400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24566
  have eq85527 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq85400
       grind)
    | exact superpose eq85400 eq9
    | exact resolve eq9 eq85400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85546 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq137 X0 x x
       have i₂ := eq85400
       grind)
    | exact superpose eq85400 eq137
    | exact resolve eq137 eq85400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85400
  have eq85594 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq85546 X0
       have i₂ := eq81 X0 x
       grind)
    | exact superpose eq81 eq85546
    | exact resolve eq85546 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq85546
  have eq86733 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq85527 X0
       have i₂ := eq85594 X0
       grind)
    | exact superpose eq85594 eq85527
    | exact resolve eq85527 eq85594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85527 eq85594
  have eq86759 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op x X0) X1) (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq137 X1 x X0
       have i₂ := eq86733 X1
       grind)
    | exact superpose eq86733 eq137
    | exact resolve eq137 eq86733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq86859 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86759 X0 X1
       have i₂ := eq86733 X0
       grind)
    | exact superpose eq86733 eq86759
    | exact resolve eq86759 eq86733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86759
  have eq88681 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq85462 X0
       have i₂ := eq86859 (σ x) X0
       grind)
    | exact superpose eq86859 eq85462
    | exact resolve eq85462 eq86859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85462 eq86859
  have eq88684 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq88681 (σ y)
       grind)
    | exact superpose eq88681 eq16
    | exact resolve eq16 eq88681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88681
  have eq88746 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq88684
       have i₂ := eq86733 y
       grind)
    | exact superpose eq86733 eq88684
    | exact resolve eq88684 eq86733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86733 eq88684
  have eq88747 : False := by grind
  exact eq88747

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X0) = (M.op X2 X2) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq45 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X0) = (M.op X2 X2) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq30 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq105 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq504 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq505 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq504 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq510 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq505 X0 X1
       have j1 := eq105 X0 X1
       grind)
    | (have r₁ := eq505 X0 X1
       have r₂ := eq105 X0 X1
       grind)
    | (have r₁ := eq505 X1 X1
       have r₂ := eq105 X1 X1
       grind)
    | exact resolve eq505 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq505
  have eq687 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq510 (σ X0) (σ X1)
       grind)
    | exact superpose eq510 eq15
    | exact resolve eq15 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq687 X0 X1
       have i₂ := eq510 X0 X1
       grind)
    | exact superpose eq510 eq687
    | exact resolve eq687 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq687
  have eq694 : False := by grind
  exact eq694

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq44
    | (have j1 := eq74 x x
       grind)
    | exact resolve eq44 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
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
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq106
    | exact resolve eq106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq121 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq37
  have eq700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq107 eq74
    | (have j0 := eq74 (σ x) x
       grind)
    | exact resolve eq74 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq700
    | exact resolve eq700 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq704 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq701
       have r₂ := eq27
       grind)
    | exact resolve eq701 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq717 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq704 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq704
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq704
       grind)
    | exact resolve eq13 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq717 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq747 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq718 eq49
    | exact resolve eq49 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq718
  have eq775 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq704 eq747
    | exact resolve eq747 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704 eq747
  have eq788 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by grind
  clear eq775
  have eq790 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq788
    | exact resolve eq788 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq788
  have eq793 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74 x x
       have i₂ := eq790
       grind)
    | exact superpose eq790 eq74
    | (have j0 := eq74 x x
       grind)
    | exact resolve eq74 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq794 : x = (M.op x x) := by grind
  clear eq793
  have eq810 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq794
       grind)
    | exact superpose eq794 eq53
    | exact resolve eq53 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq811 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq794
       grind)
    | exact superpose eq794 eq50
    | exact resolve eq50 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq812 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq794
       grind)
    | exact superpose eq794 eq14
    | exact resolve eq14 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq794
       grind)
    | exact superpose eq794 eq14
    | exact resolve eq14 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq794
       grind)
    | exact superpose eq794 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq794
       grind)
    | exact resolve eq13 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq821 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq853 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq822 x
       grind)
    | exact superpose eq822 eq43
    | exact resolve eq43 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq855 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq822 sF0
       grind)
    | exact superpose eq822 eq121
    | exact resolve eq121 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq822
  have eq861 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq853
       have i₂ := eq794
       grind)
    | exact superpose eq794 eq853
    | exact resolve eq853 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq853
  have eq862 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq861
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq861
    | exact resolve eq861 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq867 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq862 eq74
    | (have j0 := eq74 (σ x) x
       grind)
    | exact resolve eq74 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq862
  have eq868 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq867
  have eq897 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq868 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq868
       grind)
    | exact resolve eq13 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq898 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq897 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq955 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq898 eq855
    | exact resolve eq855 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq898
  have eq1041 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq813 (M.op x X0)
       have i₂ := eq812 X0
       grind)
    | exact superpose eq812 eq813
    | exact resolve eq813 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1046 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq810 eq813
    | exact resolve eq813 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1055 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1046 eq810
    | exact resolve eq810 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq1046
  have eq1071 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1055 eq955
    | exact resolve eq955 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1072 : y = (M.op x y) := by
    first
    | exact superpose eq1055 eq811
    | exact resolve eq811 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq1055
  have eq1080 : y = (M.op x y) := by
    first
    | (have i₁ := eq1072
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1072
    | exact resolve eq1072 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1072
  have eq1081 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1071
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1071
    | exact resolve eq1071 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1071
  have eq1082 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1080 eq20
    | exact resolve eq20 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1080
  have eq1115 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1082
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1082
    | exact resolve eq1082 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1082
  have eq1118 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1115 eq26
    | exact resolve eq26 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1115
  have eq1223 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq812 X0
       have i₂ := eq1041 X0
       grind)
    | exact superpose eq1041 eq812
    | exact resolve eq812 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq1041
  have eq1340 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq813 X0
       have i₂ := eq1223 X0
       grind)
    | exact superpose eq1223 eq813
    | exact resolve eq813 eq1223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq1223
  have eq1363 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 x X0
       have i₂ := eq1340 X0
       grind)
    | exact superpose eq1340 eq14
    | exact resolve eq14 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1383 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1363 X0 X1
       have i₂ := eq1340 X1
       grind)
    | exact superpose eq1340 eq1363
    | exact resolve eq1363 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340 eq1363
  have eq1512 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1081 eq1383
    | exact resolve eq1383 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq1383
  have eq1536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1118 eq1512
    | exact resolve eq1512 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118 eq1512
  have eq1553 : False := by grind
  exact eq1553

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyy_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq27 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq53 X1 x x X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq65 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X1 (M.op X1 X0)
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq95 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X2) (M.op X1 X0)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X2) X1 X0
       have i₂ := eq78 X2 X1
       grind)
    | exact superpose eq78 eq9
    | exact resolve eq9 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq108 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq108
    | (have j0 := eq108 (σ X0)
       grind)
    | exact resolve eq108 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq399 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq944 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq59 (σ X0)
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq59
    | (have j1 := eq132 X0
       grind)
    | exact resolve eq59 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq951 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq132 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq1083 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ (k X0 X0))) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq944 (τ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq944
    | (have j0 := eq944 (τ X0)
       grind)
    | exact resolve eq944 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq944
  have eq1115 : ∀ X0 : G, (M.op (σ (τ (k X0 X0))) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1083 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1083
    | (have j0 := eq1083 X0
       grind)
    | exact resolve eq1083 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1116 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1115 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq1115
    | (have j0 := eq1115 X0
       grind)
    | exact resolve eq1115 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1117 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1116 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1116
    | (have j0 := eq1116 X0
       grind)
    | exact resolve eq1116 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq3092 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq399 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq399 X0 X1
       grind)
    | exact superpose eq399 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq399 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq399 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq399 X0 X1
       grind)
    | exact resolve eq13 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq3172 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3092 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3092
  have eq3173 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3172
  have eq3203 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3173 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3173
    | (have j0 := eq3173 X0 X1
       grind)
    | exact resolve eq3173 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173
  have eq3204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3203 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3203
  have eq3217 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3204 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3204
    | exact resolve eq3204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3204
  have eq3356 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3217 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3217
    | (have j0 := eq3217 X0 X1
       grind)
    | exact resolve eq3217 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3217
  have eq3357 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3356 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3356
    | (have j0 := eq3356 X1 X1
       grind)
    | exact resolve eq3356 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3356
  have eq3563 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq3357 (τ X0) X1
       grind)
    | exact superpose eq3357 eq17
    | (have j1 := eq3357 X0 X1
       grind)
    | exact resolve eq17 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq3566 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (k X2 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq3357 X0 X1
       grind)
    | exact superpose eq3357 eq12
    | (have j1 := eq3357 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq3357 X0 X1
       grind)
    | exact resolve eq12 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357
  have eq3670 : ∀ X0 X1 X2 : G, (k X2 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3566 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566
  have eq3776 : ∀ X0 X1 X2 : G, (τ X2) = (k X0 (τ X2)) ∨ (M.op X2 X1) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X2 X0
       have i₂ := eq3670 X1 X2 (σ X0)
       grind)
    | exact superpose eq3670 eq27
    | (have j1 := eq3670 X0 (τ X2) X0
       grind)
    | exact resolve eq27 eq3670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq3806 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3670 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3670
  have eq3823 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3806 (M.op X0 X1) X0
       have i₂ := eq78 X1 X0
       grind)
    | exact superpose eq78 eq3806
    | (have j0 := eq3806 X1 X0
       grind)
    | exact resolve eq3806 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3806
  have eq4149 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3776 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3776
    | (have j0 := eq3776 X0 X2 (σ X0)
       grind)
    | exact resolve eq3776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3776
  have eq4308 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4149 X1 X2 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4149
    | (have j0 := eq4149 X1 X2 X2
       grind)
    | exact resolve eq4149 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4149
  have eq5805 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3563 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3563
    | (have j0 := eq3563 X0 X1
       grind)
    | exact resolve eq3563 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3563
  have eq5996 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5805 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5805
    | (have j0 := eq5805 X0 X1
       grind)
    | exact resolve eq5805 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5805
  have eq7716 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq4308 y x X0
       grind)
    | exact superpose eq4308 eq16
    | (have j1 := eq4308 X0 x X0
       grind)
    | exact resolve eq16 eq4308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4308
  have eq7880 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k X0 x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq7716 X0
       have i₂ := eq5996 y x
       grind)
    | exact superpose eq5996 eq7716
    | (have j0 := eq7716 X0
       have j1 := eq5996 X0 x
       grind)
    | (have r₁ := eq7716 X0
       have r₂ := eq5996 y x
       grind)
    | exact resolve eq7716 eq5996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5996 eq7716
  have eq7882 : ∀ X0 : G, x = (k X0 x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq7880 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7880
  have eq7908 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1117 x
       have i₂ := eq7882 x
       grind)
    | exact superpose eq7882 eq1117
    | (have j0 := eq1117 x
       grind)
    | exact resolve eq1117 eq7882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117 eq7882
  have eq7950 : x = (M.op x x) := by grind
  clear eq7908
  have eq7984 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq7950
       grind)
    | exact superpose eq7950 eq9
    | exact resolve eq9 eq7950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7997 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq95 X0 x x
       have i₂ := eq7950
       grind)
    | exact superpose eq7950 eq95
    | exact resolve eq95 eq7950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8005 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq3823 x x
       have i₂ := eq7950
       grind)
    | exact superpose eq7950 eq3823
    | (have r₁ := eq3823 x x
       have r₂ := eq7950
       grind)
    | exact resolve eq3823 eq7950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3823 eq7950
  have eq8006 : x = (k x x) := by grind
  clear eq8005
  have eq8012 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq7997 X0
       have i₂ := eq78 X0 x
       grind)
    | exact superpose eq78 eq7997
    | exact resolve eq7997 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq7997
  have eq8030 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq951 x
       have i₂ := eq8006
       grind)
    | exact superpose eq8006 eq951
    | (have j0 := eq951 x
       grind)
    | exact resolve eq951 eq8006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951 eq8006
  have eq8045 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8030
  have eq8288 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ x)
       have i₂ := eq8045
       grind)
    | exact superpose eq8045 eq9
    | exact resolve eq9 eq8045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8045
  have eq8430 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7984 X0
       have i₂ := eq8012 X0
       grind)
    | exact superpose eq8012 eq7984
    | exact resolve eq7984 eq8012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7984 eq8012
  have eq8446 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op x X0) X1) (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X1 x X0
       have i₂ := eq8430 X1
       grind)
    | exact superpose eq8430 eq95
    | exact resolve eq95 eq8430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq8485 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8446 X0 X1
       have i₂ := eq8430 X0
       grind)
    | exact superpose eq8430 eq8446
    | exact resolve eq8446 eq8430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8446
  have eq9143 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8288 X0
       have i₂ := eq8485 (σ x) X0
       grind)
    | exact superpose eq8485 eq8288
    | exact resolve eq8288 eq8485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8288 eq8485
  have eq9146 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9143 (σ y)
       grind)
    | exact superpose eq9143 eq16
    | exact resolve eq16 eq9143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9143
  have eq9177 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq9146
       have i₂ := eq8430 y
       grind)
    | exact superpose eq8430 eq9146
    | exact resolve eq9146 eq8430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8430 eq9146
  have eq9178 : False := by grind
  exact eq9178
