import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq55 (τ X0)
       grind)
    | exact superpose eq55 eq18
    | exact resolve eq18 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq63
    | exact resolve eq63 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq63
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq13
    | exact resolve eq13 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq129 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X0 (M.op X1 (M.op X2 X0))) X1 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq266 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | (have j0 := eq93 X1 X1
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq283 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq266 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq266
    | (have j0 := eq266 X0 X1
       grind)
    | exact resolve eq266 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq289 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq283 X0 X1
       have j1 := eq80 X1 X0
       grind)
    | (have r₁ := eq283 X0 X0
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq283 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq384 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq289 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq289
    | exact resolve eq289 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq289 (σ X1) X0
       grind)
    | exact superpose eq289 eq15
    | (have j1 := eq289 (σ X1) X0
       grind)
    | exact resolve eq15 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq408 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq384 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq384
    | (have j0 := eq384 X0 X1
       grind)
    | exact resolve eq384 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq384
  have eq428 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq408 X0 (τ X1)
       grind)
    | exact superpose eq408 eq17
    | (have j1 := eq408 X0 (τ X1)
       grind)
    | exact resolve eq17 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq408
  have eq498 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op X1 (M.op X2 (σ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129 (σ X0) (σ X0) X2 x
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq129
    | exact resolve eq129 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq1077 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq428 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq428
    | exact resolve eq428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq1123 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1077 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1077
    | (have j0 := eq1077 X0 X1
       grind)
    | exact resolve eq1077 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq4118 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq395 x y
       grind)
    | exact superpose eq395 eq16
    | (have j1 := eq395 x y
       grind)
    | exact resolve eq16 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4159 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq395 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq4193 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4118
       have i₂ := eq1123 y x
       grind)
    | exact superpose eq1123 eq4118
    | (have j1 := eq1123 y x
       grind)
    | (have r₁ := eq4118
       have r₂ := eq1123 y x
       grind)
    | exact resolve eq4118 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4118
  have eq4194 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4193
  have eq4294 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq4194
       grind)
    | exact superpose eq4194 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4194
       grind)
    | exact resolve eq13 eq4194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4194
  have eq4311 : (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4294
  have eq36767 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4159 x y
       have i₂ := eq4311
       grind)
    | exact superpose eq4311 eq4159
    | (have j0 := eq4159 x y
       grind)
    | exact resolve eq4159 eq4311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4159 eq4311
  have eq36778 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq36767
  have eq36779 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq36778
  have eq37001 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36779
       grind)
    | exact superpose eq36779 eq16
    | exact resolve eq16 eq36779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37002 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq79 x (σ y)
       have i₂ := eq36779
       grind)
    | exact superpose eq36779 eq79
    | (have j0 := eq79 x (σ y)
       grind)
    | (have r₁ := eq79 x (σ y)
       have r₂ := eq36779
       grind)
    | exact resolve eq79 eq36779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq36779
  have eq37055 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq37002
  have eq37058 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq37055
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq37055
    | exact resolve eq37055 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37055
  have eq37701 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1123 y x
       have i₂ := eq37058
       grind)
    | exact superpose eq37058 eq1123
    | (have j0 := eq1123 y x
       grind)
    | exact resolve eq1123 eq37058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123 eq37058
  have eq37824 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq37701
       have r₂ := eq37001
       grind)
    | exact resolve eq37701 eq37001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37701
  have eq38064 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq37001
       have i₂ := eq37824
       grind)
    | exact superpose eq37824 eq37001
    | exact resolve eq37001 eq37824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37001 eq37824
  have eq38110 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq38064
  have eq38111 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq38110
  have eq38303 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq80 x X0
       have i₂ := eq38111
       grind)
    | exact superpose eq38111 eq80
    | (have j0 := eq80 x X0
       grind)
    | (have r₁ := eq80 x x
       have r₂ := eq38111
       grind)
    | exact resolve eq80 eq38111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38309 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op X0 (M.op X1 (σ x)))))) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq498 x X1 x
       have i₂ := eq38111
       grind)
    | exact superpose eq38111 eq498
    | exact resolve eq498 eq38111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq38111
  have eq38394 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq38303 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38303
  have eq38403 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq38309 x x
       have i₂ := eq9 (σ x) x x
       grind)
    | exact superpose eq9 eq38309
    | exact resolve eq38309 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38309
  have eq38404 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq38394 X0
       have j1 := eq80 x X0
       grind)
    | (have r₁ := eq38394 X0
       have r₂ := eq80 x x
       grind)
    | exact resolve eq38394 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq38394
  have eq38407 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq38403
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq38403
    | exact resolve eq38403 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq38403
  have eq38408 : (σ x) = (σ (M.op x x)) := by grind
  clear eq38407
  have eq38428 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq38408
       grind)
    | exact superpose eq38408 eq10
    | exact resolve eq10 eq38408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38408
  have eq38550 : x = (M.op x x) := by
    first
    | (have i₁ := eq38428
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq38428
    | exact resolve eq38428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38428
  have eq38747 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq38550
       grind)
    | exact superpose eq38550 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq38550
       grind)
    | exact resolve eq12 eq38550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38550
  have eq38841 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq38747 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38747
  have eq39700 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq38404 (σ X0)
       grind)
    | exact superpose eq38404 eq15
    | exact resolve eq15 eq38404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38404
  have eq39835 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq39700 X0
       have i₂ := eq38841 X0
       grind)
    | exact superpose eq38841 eq39700
    | exact resolve eq39700 eq38841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38841 eq39700
  have eq41171 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39835 y
       grind)
    | exact superpose eq39835 eq16
    | (have r₁ := eq16
       have r₂ := eq39835 y
       grind)
    | exact resolve eq16 eq39835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39835
  have eq41349 : False := by grind
  exact eq41349

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq51 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq51 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq51 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq52 (σ X0)
       grind)
    | exact superpose eq52 eq15
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  clear eq52 eq54
  have eq74 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq83
  have eq133 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq137 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq141 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq137 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq137 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq151 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       have j1 := eq74 X1 (σ X0)
       grind)
    | (have r₁ := eq141 X0 X0
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq141 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq141
  have eq158 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq151
    | (have j0 := eq151 X0 X1
       grind)
    | exact resolve eq151 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq159 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq158 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq165 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq159 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq159
    | exact resolve eq159 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq159 x y
       grind)
    | exact superpose eq159 eq16
    | exact resolve eq16 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq258 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq165 X0 (τ X1)
       grind)
    | exact superpose eq165 eq18
    | exact resolve eq18 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq165
  have eq275 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq258 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq258
    | exact resolve eq258 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq283 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq275
    | exact resolve eq275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq406 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq176
       have i₂ := eq283 x y
       grind)
    | exact superpose eq283 eq176
    | exact resolve eq176 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq283
  have eq407 : False := by grind
  exact eq407

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_x_pyy_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq174 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq16 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq16 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq174 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y x
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (M.op X1 X0) X0
       have i₂ := eq174 X0 X1
       grind)
    | exact superpose eq174 eq174
    | exact resolve eq174 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq176 eq174
    | exact resolve eq174 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq176
  have eq191 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq175 X0 (M.op X0 X0)
       grind)
    | exact superpose eq175 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq175 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq382 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op X1 X1)
       have i₂ := eq193 X1 (τ X0)
       grind)
    | exact superpose eq193 eq34
    | exact resolve eq34 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq410 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq382 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq382
    | exact resolve eq382 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq527 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq559 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq527 X0 (M.op X1 X1)
       have i₂ := eq193 X1 (σ X0)
       grind)
    | exact superpose eq193 eq527
    | exact resolve eq527 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq527
  have eq720 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq690 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq690
    | exact resolve eq690 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq1056 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X0) = X0 ∨ (k X1 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq623 X0
       grind)
    | exact superpose eq623 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq623 X0
       grind)
    | exact resolve eq12 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1057 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq623 X0
       grind)
    | exact superpose eq623 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq623 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq623 X0
       grind)
    | exact resolve eq13 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1095 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq179 X0 X0
       have i₂ := eq623 X0
       grind)
    | exact superpose eq623 eq179
    | (have j1 := eq623 X0
       grind)
    | exact resolve eq179 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1098 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq623 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1103 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1057 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq1057 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq1057 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1057 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1104 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X0) = X0 ∨ (k X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1056 X0 X1
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1056 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1056 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq559
       grind)
    | exact superpose eq559 eq40
    | exact resolve eq40 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq1108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1107
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1107
    | exact resolve eq1107 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1108
    | exact resolve eq1108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1113 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1098 (σ (M.op X0 X0))
       have i₂ := eq410 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq410 eq1098
    | (have j0 := eq1098 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq1098 (σ (M.op x x))
       have r₂ := eq410 (σ (M.op x x)) x
       grind)
    | exact resolve eq1098 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq1117 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1098 (τ (M.op X0 X0))
       have i₂ := eq720 (τ (M.op X0 X0)) X0
       grind)
    | exact superpose eq720 eq1098
    | (have j0 := eq1098 (τ (M.op X0 X0))
       grind)
    | (have r₁ := eq1098 (τ (M.op x x))
       have r₂ := eq720 (τ (M.op x x)) x
       grind)
    | exact resolve eq1098 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq1124 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1128 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1985 : ∀ X0 X1 : G, (k X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X0 X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 X0
       have i₂ := eq623 X0
       grind)
    | exact superpose eq623 eq580
    | (have j0 := eq580 X0 X0
       have j1 := eq623 X0
       grind)
    | (have r₁ := eq580 X0 X0
       have r₂ := eq623 X0
       grind)
    | exact resolve eq580 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq2002 : ∀ X0 X1 : G, (k X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1985 X0 X1
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1985 X1 (k X1 X1)
       have r₂ := eq13 (k X1 X1) X1
       grind)
    | (have r₁ := eq1985 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1985 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1985
  have eq13196 : ∀ X0 : G, (M.op X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (k X0 X0) X0
       have i₂ := eq1095 X0
       grind)
    | exact superpose eq1095 eq12
    | (have j0 := eq12 (k X0 X0) X0
       have j1 := eq1095 X0
       grind)
    | exact resolve eq12 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq13203 : ∀ X0 : G, (M.op X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13196 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13196
  have eq13234 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13203 X0
       have j1 := eq623 X0
       grind)
    | (have r₁ := eq13203 X0
       have r₂ := eq623 X0
       grind)
    | exact resolve eq13203 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13203
  have eq13236 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq623 eq13234
    | (have j0 := eq13234 X0
       have j1 := eq623 X0
       grind)
    | exact resolve eq13234 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13234
  have eq13238 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13236 X0
       have j1 := eq13 (k X0 X0) X0
       grind)
    | (have r₁ := eq13236 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq13236 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13236
  have eq21850 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq175 (σ (M.op X0 X0)) X1
       have i₂ := eq1128 X0
       grind)
    | exact superpose eq1128 eq175
    | exact resolve eq175 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq28461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1110 eq562
    | exact resolve eq562 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28468 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq28461
       have r₂ := eq27
       grind)
    | exact resolve eq28461 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28461
  have eq28474 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq623 eq28468
    | (have j1 := eq623 (σ y)
       grind)
    | exact resolve eq28468 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28468
  have eq28644 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq28474 eq1098
    | (have j0 := eq1098 (σ y)
       grind)
    | exact resolve eq1098 eq28474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq28657 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq28644
  have eq30719 : (M.op x y) ≠ (k y y) ∨ y = (k y y) ∨ (k x y) = (k y y) := by
    first
    | (have i₁ := eq1104 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1104
    | (have j0 := eq1104 y x
       grind)
    | exact resolve eq1104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30721 : (M.op x y) ≠ (k y y) ∨ y = (k y y) ∨ (k y y) = (k (M.op x y) y) := by
    first
    | exact superpose eq183 eq1104
    | (have j0 := eq1104 y x
       grind)
    | exact resolve eq1104 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq30726 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1104
    | (have j0 := eq1104 (σ y) (σ x)
       grind)
    | exact resolve eq1104 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq30732 : (M.op x y) ≠ (k y y) ∨ y = (k y y) ∨ (k x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq30721 eq30719
    | exact resolve eq30719 eq30721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30719 eq30721
  have eq33312 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2002 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq54315 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq28474 eq30726
    | (have r₁ := eq30726
       have r₂ := eq28474
       grind)
    | exact resolve eq30726 eq28474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28474 eq30726
  have eq54322 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq54315
  have eq54323 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq54322
       have r₂ := eq28657
       grind)
    | exact resolve eq54322 eq28657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28657 eq54322
  have eq54324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1110 eq54323
    | exact resolve eq54323 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq54323
  have eq54325 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq54324
       have r₂ := eq27
       grind)
    | exact resolve eq54324 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54324
  have eq54372 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq54325 eq1124
    | exact resolve eq1124 eq54325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54325
  have eq54445 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq54372
    | exact resolve eq54372 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54372
  have eq54446 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq54445
  have eq54501 : (M.op x y) = (k y y) ∨ y = (k y y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq54446
       have i₂ := eq33312 y
       grind)
    | exact superpose eq33312 eq54446
    | (have j1 := eq33312 y
       grind)
    | exact resolve eq54446 eq33312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33312
  have eq54587 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq54446
       grind)
    | exact superpose eq54446 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq54446
       grind)
    | exact resolve eq12 eq54446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54595 : y ≠ (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq54446
  have eq54596 : y = (M.op x y) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by grind
  clear eq54587
  have eq54597 : (M.op x y) = (k y y) ∨ y = (k y y) := by grind
  clear eq54501
  have eq54598 : (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq54596
       have r₂ := eq54595
       grind)
    | exact resolve eq54596 eq54595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54596
  have eq55345 : (M.op x y) = (k (M.op x y) y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq13238 y
       have i₂ := eq54597
       grind)
    | exact superpose eq54597 eq13238
    | exact resolve eq13238 eq54597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13238 eq54597
  have eq55357 : (M.op x y) = (k (M.op x y) y) := by
    first
    | (have j1 := eq1103 y (M.op x y)
       grind)
    | (have r₁ := eq55345
       have r₂ := eq1103 y x
       grind)
    | exact resolve eq55345 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq55345
  have eq55429 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq54598
       grind)
    | exact superpose eq54598 eq40
    | exact resolve eq40 eq54598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55473 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq55429
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq55429
    | exact resolve eq55429 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55429
  have eq55479 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq55473
    | exact resolve eq55473 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55473
  have eq56754 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (k x y) = (k (M.op x y) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq30732
       have i₂ := eq54598
       grind)
    | exact superpose eq54598 eq30732
    | (have r₁ := eq30732
       have r₂ := eq54598
       grind)
    | exact resolve eq30732 eq54598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30732 eq54598
  have eq56757 : y = (M.op x y) ∨ (k x y) = (k (M.op x y) y) ∨ y = (M.op y y) := by grind
  clear eq56754
  have eq56763 : (k x y) = (k (M.op x y) y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq56757
       have r₂ := eq54595
       grind)
    | exact resolve eq56757 eq54595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54595 eq56757
  have eq56769 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq55357 eq56763
    | exact resolve eq56763 eq55357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55357 eq56763
  have eq61732 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq56769
       grind)
    | exact superpose eq56769 eq40
    | exact resolve eq40 eq56769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq56769
  have eq61736 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq61732
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq61732
    | exact resolve eq61732 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61732
  have eq61740 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq61736
    | exact resolve eq61736 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61736
  have eq62348 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq61740 eq562
    | exact resolve eq562 eq61740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq61740
  have eq62363 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq62348
       have r₂ := eq27
       grind)
    | exact resolve eq62348 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62348
  have eq62369 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq623 eq62363
    | (have j1 := eq623 (σ y)
       grind)
    | exact resolve eq62363 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq62363
  have eq62372 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq55479 eq62369
    | exact resolve eq62369 eq55479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55479 eq62369
  have eq62374 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq62372
       have r₂ := eq27
       grind)
    | exact resolve eq62372 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62372
  have eq62638 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq62374 eq1124
    | exact resolve eq1124 eq62374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124 eq62374
  have eq62698 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq62638
    | exact resolve eq62638 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq62638
  have eq62699 : y = (M.op y y) := by grind
  clear eq62698
  have eq63237 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 y X0
       have i₂ := eq62699
       grind)
    | exact superpose eq62699 eq175
    | exact resolve eq175 eq62699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq63299 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq21850 y X0
       have i₂ := eq62699
       grind)
    | exact superpose eq62699 eq21850
    | exact resolve eq21850 eq62699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21850 eq62699
  have eq63326 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq63299 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq63299
    | (have j0 := eq63299 X0
       grind)
    | exact resolve eq63299 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq63299
  have eq63519 : x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq63237 x
       grind)
    | exact superpose eq63237 eq18
    | (have j1 := eq63237 x
       grind)
    | exact resolve eq18 eq63237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq63237
  have eq63562 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq63519
       grind)
    | exact superpose eq63519 eq22
    | exact resolve eq22 eq63519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq63519
  have eq63624 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq63562 eq20
    | exact resolve eq20 eq63562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq63562
  have eq64864 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63326 eq26
    | (have j1 := eq63326 (σ x)
       grind)
    | exact resolve eq26 eq63326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq63326
  have eq64903 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq64864 eq27
    | exact resolve eq27 eq64864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq64864
  have eq65053 : False := by grind
  exact eq65053

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_x_pxy_Equation4419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X1) X0) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X2 X1) X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X1)) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X0 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 (M.op x X1)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
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
  have eq79 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq103
    | exact resolve eq103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq114
    | exact resolve eq114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq116
    | exact resolve eq116 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq213 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 y)
       have i₂ := eq213 X0 y
       grind)
    | (have i₁ := eq56 (M.op x y)
       have i₂ := eq213 X0 y
       grind)
    | exact superpose eq213 eq56
    | exact resolve eq56 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq57 (M.op X0 y)
       have i₂ := eq213 X0 sF3
       grind)
    | (have i₁ := eq57 (M.op x y)
       have i₂ := eq213 X0 sF3
       grind)
    | exact superpose eq213 eq57
    | exact resolve eq57 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq373 X0
       have i₂ := eq213 X0 (M.op sF0 sF3)
       grind)
    | (have i₁ := eq373 x
       have i₂ := eq213 X0 (M.op sF0 sF3)
       grind)
    | exact superpose eq213 eq373
    | exact resolve eq373 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq375 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq213 X0 (M.op sF0 y)
       grind)
    | (have i₁ := eq372 x
       have i₂ := eq213 X0 (M.op sF0 y)
       grind)
    | exact superpose eq213 eq372
    | exact resolve eq372 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq384 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq57 eq374
    | exact resolve eq374 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq385 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq375 X0
       have i₂ := eq56 sF0
       grind)
    | exact superpose eq56 eq375
    | exact resolve eq375 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq395 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X2 (M.op X0 y)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 (M.op X0 y) X1 X2
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op X2 (M.op X0 (σ y))) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq53
    | exact resolve eq53 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq222 eq56
    | exact resolve eq56 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq222 eq490
    | exact resolve eq490 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq503 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq493 X0
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq493
    | exact resolve eq493 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq548 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X1 X2 X3
       have i₂ := eq53 X1 (M.op X1 X2) X3 X0
       grind)
    | (have i₁ := eq55 X1 X2 X3
       have i₂ := eq53 X0 (M.op X1 X2) X3 X1
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq648 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq384 sF4
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq384
    | exact resolve eq384 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq697 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 y X0 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq51
    | exact resolve eq51 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq57 eq51
    | exact resolve eq51 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq792 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq222 eq698
    | (have j0 := eq698 X0 (σ x)
       grind)
    | exact resolve eq698 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq793 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq697 X0 x
       have i₂ := eq213 x X0
       grind)
    | (have i₁ := eq697 x x
       have i₂ := eq213 X0 x
       grind)
    | exact superpose eq213 eq697
    | (have j0 := eq697 X0 x
       grind)
    | exact resolve eq697 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq1156 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X0 X1)
       have i₂ := eq52 X1 y (M.op X0 X1) X0
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1207 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1156 X0 X1
       have i₂ := eq213 (M.op X0 X1) (M.op X1 (M.op X1 y))
       grind)
    | exact superpose eq213 eq1156
    | exact resolve eq1156 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1233 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1207 X0 X1
       have i₂ := eq56 X1
       grind)
    | exact superpose eq56 eq1207
    | exact resolve eq1207 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1613 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq2092 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq222 eq792
    | exact resolve eq792 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq792
  have eq2217 : (M.op (M.op x y) y) = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq793 y
       have i₂ := eq213 sF0 y
       grind)
    | exact superpose eq213 eq793
    | exact resolve eq793 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2271 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2217 eq51
    | exact resolve eq51 eq2217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2296 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2271 X0
       have i₂ := eq14 sF0 y sF0
       grind)
    | exact superpose eq14 eq2271
    | exact resolve eq2271 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271
  have eq2301 : (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq2296 x
       have i₂ := eq14 sF0 y x
       grind)
    | exact superpose eq14 eq2296
    | exact resolve eq2296 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296
  have eq2302 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2301
       have i₂ := eq56 sF0
       grind)
    | exact superpose eq56 eq2301
    | exact resolve eq2301 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2301
  have eq2615 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq1233 X0 (M.op X0 y)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq1233
    | exact resolve eq1233 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2732 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq385 eq2615
    | exact resolve eq2615 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq2615
  have eq2751 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq2302 eq2732
    | exact resolve eq2732 eq2302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302 eq2732
  have eq2815 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1233 eq2751
    | exact resolve eq2751 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2816 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq503 eq2751
    | exact resolve eq2751 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq2751
  have eq4094 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (M.op y X1)) y) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq395 (M.op X2 X1) X3 y
       have i₂ := eq51 X2 X1 y X0
       grind)
    | exact superpose eq51 eq395
    | exact resolve eq395 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq4285 : ∀ X1 X2 X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op X2 X1)) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq4094 x X1 X2 X3
       have i₂ := eq213 (M.op x (M.op y X1)) X3
       grind)
    | exact superpose eq213 eq4094
    | exact resolve eq4094 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4094
  have eq4347 : ∀ X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X3
    first
    | exact superpose eq2815 eq4285
    | (have j0 := eq4285 y x X3
       grind)
    | exact resolve eq4285 eq2815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2815 eq4285
  have eq4606 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op X2 (M.op (M.op x y) (σ y))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq396 (M.op X0 y) X1 X2
       have i₂ := eq213 X0 sF3
       grind)
    | (have i₁ := eq396 (M.op x y) X1 X2
       have i₂ := eq213 X0 sF3
       grind)
    | exact superpose eq213 eq396
    | exact resolve eq396 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4833 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq396 eq4606
    | exact resolve eq4606 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq4606
  have eq4894 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq648 eq4833
    | exact resolve eq4833 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648 eq4833
  have eq4942 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq2816 eq4894
    | exact resolve eq4894 eq2816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2816 eq4894
  have eq4980 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq4347 eq4942
    | exact resolve eq4942 eq4347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4347 eq4942
  have eq5004 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4980 X0 X1
       have i₂ := eq395 X0 X1 sF4
       grind)
    | exact superpose eq395 eq4980
    | exact resolve eq4980 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq4980
  have eq5834 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5004 X1 X2
       have i₂ := eq53 sF0 X1 X2 x
       grind)
    | (have i₁ := eq5004 X1 X2
       have i₂ := eq53 X0 X1 X2 sF0
       grind)
    | exact superpose eq53 eq5004
    | exact resolve eq5004 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6996 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq1233 eq548
    | exact resolve eq548 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq1233
  have eq7313 : ∀ X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op x y) X2) := by
    intro X1 X2
    first
    | exact superpose eq5004 eq6996
    | exact resolve eq6996 eq5004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5004 eq6996
  have eq18467 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18468 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18467
    | exact resolve eq18467 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18467
  have eq18479 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18468
       have r₂ := eq28
       grind)
    | exact resolve eq18468 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18468
  have eq18481 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18479
    | exact resolve eq18479 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18479
  have eq18491 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  have eq18509 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq18481 eq5834
    | exact resolve eq5834 eq18481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18510 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18481 eq7313
    | exact resolve eq7313 eq18481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18481
  have eq18556 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18491 eq117
    | exact resolve eq117 eq18491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18491
  have eq18564 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18556
  have eq18663 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18509
    | (have j0 := eq18509 (σ y)
       grind)
    | exact resolve eq18509 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18509
  have eq18968 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18510 eq18564
    | exact resolve eq18564 eq18510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18510 eq18564
  have eq18991 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18968
  have eq19020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18991 eq18663
    | exact resolve eq18663 eq18991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18663 eq18991
  have eq19060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19020
  have eq19087 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19060
       have r₂ := eq28
       grind)
    | exact resolve eq19060 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19060
  have eq19108 : (M.op y x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq19087
       grind)
    | exact superpose eq19087 eq56
    | exact resolve eq56 eq19087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19109 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq213 y X0
       have i₂ := eq19087
       grind)
    | exact superpose eq19087 eq213
    | exact resolve eq213 eq19087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19115 : (k x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19087
  have eq19288 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19109 eq19108
    | exact resolve eq19108 eq19109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19108 eq19109
  have eq19373 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19288
  have eq19412 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19373
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19373
    | exact resolve eq19373 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19373
  have eq19544 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq19115
       grind)
    | exact superpose eq19115 eq45
    | exact resolve eq45 eq19115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19115
  have eq19913 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19544
       have i₂ := eq19412
       grind)
    | exact superpose eq19412 eq19544
    | exact resolve eq19544 eq19412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19412 eq19544
  have eq19954 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19913
  have eq19958 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq19954
    | exact resolve eq19954 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19954
  have eq19971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19958 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq19958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19974 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq19971
    | exact resolve eq19971 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19971
  have eq19985 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19974
       have r₂ := eq28
       grind)
    | exact resolve eq19974 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19974
  have eq19987 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq19985
    | exact resolve eq19985 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19985
  have eq19988 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19987
  have eq20022 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq20040 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19988 eq5834
    | exact resolve eq5834 eq19988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20041 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19988 eq7313
    | exact resolve eq7313 eq19988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19988
  have eq20095 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20022 eq19958
    | exact resolve eq19958 eq20022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19958 eq20022
  have eq20097 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20095
  have eq20206 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq20040
    | (have j0 := eq20040 (σ y)
       grind)
    | exact resolve eq20040 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20040
  have eq20572 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20041 eq20097
    | exact resolve eq20097 eq20041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20041 eq20097
  have eq20597 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20572
  have eq20626 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20597 eq20206
    | exact resolve eq20206 eq20597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20206 eq20597
  have eq20670 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20626
  have eq20699 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20670
       have r₂ := eq28
       grind)
    | exact resolve eq20670 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20670
  have eq20719 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20699 eq28
    | exact resolve eq28 eq20699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20720 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20699 eq79
    | (have r₁ := eq79
       have r₂ := eq20699
       grind)
    | exact resolve eq79 eq20699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq20728 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20699 eq2092
    | exact resolve eq2092 eq20699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092
  have eq20740 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20720
  have eq20743 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq20728
    | exact resolve eq20728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20728
  have eq20747 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20699 eq20743
    | exact resolve eq20743 eq20699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20699 eq20743
  have eq20772 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq20747
  have eq20826 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20772 eq7313
    | exact resolve eq7313 eq20772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21577 : (σ x) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20826 eq20772
    | exact resolve eq20772 eq20826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20826
  have eq21604 : (σ x) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21577
  have eq22225 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21604 eq793
    | exact resolve eq793 eq21604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq21604
  have eq22299 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq22225
    | exact resolve eq22225 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22225
  have eq24283 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20740 eq117
    | exact resolve eq117 eq20740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24300 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq24283
  have eq24314 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24300
       have r₂ := eq20719
       grind)
    | exact resolve eq24300 eq20719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24300
  have eq24330 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq24314
  have eq24581 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24330 eq117
    | exact resolve eq117 eq24330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq24330
  have eq24594 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq24581
  have eq24608 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24594 eq20772
    | exact resolve eq20772 eq24594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20772 eq24594
  have eq24638 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq24608
  have eq24662 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24638
       have r₂ := eq20719
       grind)
    | exact resolve eq24638 eq20719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24638
  have eq24674 : (M.op y x) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq24662
       grind)
    | exact superpose eq24662 eq56
    | exact resolve eq56 eq24662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq24675 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq213 y X0
       have i₂ := eq24662
       grind)
    | exact superpose eq24662 eq213
    | exact resolve eq213 eq24662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq24683 : (k x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq24662
  have eq24896 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24675 eq24674
    | exact resolve eq24674 eq24675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24674 eq24675
  have eq25025 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq24896
  have eq25075 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25025
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq25025
    | exact resolve eq25025 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25025
  have eq25348 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq24683
       grind)
    | exact superpose eq24683 eq45
    | exact resolve eq45 eq24683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24683
  have eq27071 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25348
       have i₂ := eq25075
       grind)
    | exact superpose eq25075 eq25348
    | exact resolve eq25348 eq25075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25075 eq25348
  have eq27114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27071
  have eq27118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq27114
    | exact resolve eq27114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27114
  have eq27135 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27118 eq20740
    | exact resolve eq20740 eq27118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20740
  have eq27141 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27135
  have eq27149 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27141
       have r₂ := eq20719
       grind)
    | exact resolve eq27141 eq20719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20719 eq27141
  have eq27178 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq27149
  have eq27292 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27178 eq27118
    | exact resolve eq27118 eq27178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27118 eq27178
  have eq27296 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq27292
  have eq27313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27296 eq22299
    | exact resolve eq22299 eq27296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22299 eq27296
  have eq27339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27313
  have eq27364 : x = (M.op x y) := by
    first
    | (have r₁ := eq27339
       have r₂ := eq28
       grind)
    | exact resolve eq27339 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27339
  have eq27375 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq27364 eq21
    | exact resolve eq21 eq27364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq27380 : x ≠ x ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq27364 eq78
    | (have r₁ := eq78
       have r₂ := eq27364
       grind)
    | exact resolve eq78 eq27364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq27438 : (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq27364 eq2217
    | exact resolve eq2217 eq27364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq27464 : x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq27380
  have eq27475 : (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq27438
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27438
    | exact resolve eq27438 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq27438
  have eq27531 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq27375
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27375
    | exact resolve eq27375 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27375
  have eq27537 : x = (M.op y x) := by
    first
    | exact superpose eq27364 eq27475
    | exact resolve eq27475 eq27364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27475
  have eq28379 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq27531 eq27
    | exact resolve eq27 eq27531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31108 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq27464
       grind)
    | exact superpose eq27464 eq45
    | exact resolve eq45 eq27464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31122 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1613 x y
       have i₂ := eq27464
       grind)
    | exact superpose eq27464 eq1613
    | (have j0 := eq1613 x y
       grind)
    | exact resolve eq1613 eq27464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27464
  have eq31125 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq31122
  have eq31132 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31125
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31125
    | exact resolve eq31125 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31125
  have eq31142 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27531 eq31108
    | exact resolve eq31108 eq27531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31108
  have eq31144 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31132
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31132
    | exact resolve eq31132 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31132
  have eq31154 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31142
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31142
    | exact resolve eq31142 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31142
  have eq31155 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq31144
    | exact resolve eq31144 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31144
  have eq31163 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27531 eq31154
    | exact resolve eq31154 eq27531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31154
  have eq31164 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27531 eq31155
    | exact resolve eq31155 eq27531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31155
  have eq31168 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq31164
       have r₂ := eq28
       grind)
    | exact resolve eq31164 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31164
  have eq31172 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31168
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31168
    | exact resolve eq31168 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31168
  have eq31176 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31172
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31172
    | exact resolve eq31172 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31172
  have eq31180 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27531 eq31176
    | exact resolve eq31176 eq27531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31176
  have eq31254 : (M.op (σ y) (σ (M.op x y))) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by grind
  have eq31272 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq31180 eq5834
    | exact resolve eq5834 eq31180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31273 : (M.op (σ y) (σ (M.op x y))) = (M.op (M.op x y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31180 eq7313
    | exact resolve eq7313 eq31180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31180
  have eq31286 : (M.op (σ y) (σ (M.op x y))) = (M.op x (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27364 eq31273
    | exact resolve eq31273 eq27364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31273
  have eq31287 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq27364 eq31272
    | exact resolve eq31272 eq27364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31272
  have eq38025 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31254 eq31163
    | exact resolve eq31163 eq31254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31163 eq31254
  have eq38034 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y y) := by grind
  clear eq38025
  have eq38157 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31286 eq38034
    | exact resolve eq38034 eq31286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31286 eq38034
  have eq38185 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (M.op y y) := by grind
  clear eq38157
  have eq38317 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28379 eq31287
    | exact resolve eq31287 eq28379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31287
  have eq38543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq38317 eq38185
    | exact resolve eq38185 eq38317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38185 eq38317
  have eq38580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq38543
  have eq38598 : x = (M.op y y) := by
    first
    | (have r₁ := eq38580
       have r₂ := eq28
       grind)
    | exact resolve eq38580 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38580
  have eq38627 : (k x y) = (M.op y x) := by grind
  clear eq38598
  have eq38670 : x = (k x y) := by
    first
    | (have i₁ := eq38627
       have i₂ := eq27537
       grind)
    | exact superpose eq27537 eq38627
    | exact resolve eq38627 eq27537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27537 eq38627
  have eq38701 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq38670
       grind)
    | exact superpose eq38670 eq45
    | exact resolve eq45 eq38670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq38713 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1613 x y
       have i₂ := eq38670
       grind)
    | exact superpose eq38670 eq1613
    | (have j0 := eq1613 x y
       grind)
    | exact resolve eq1613 eq38670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613 eq38670
  have eq38720 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq38713
  have eq38733 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq38720
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38720
    | exact resolve eq38720 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38720
  have eq38740 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq27531 eq38701
    | exact resolve eq38701 eq27531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38701
  have eq38747 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq38733
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38733
    | exact resolve eq38733 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38733
  have eq38754 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq38740
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38740
    | exact resolve eq38740 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38740
  have eq38761 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq38747
    | exact resolve eq38747 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq38747
  have eq38766 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq27531 eq38754
    | exact resolve eq38754 eq27531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38754
  have eq38773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27531 eq38761
    | exact resolve eq38761 eq27531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38761
  have eq38780 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq38773
       have r₂ := eq28
       grind)
    | exact resolve eq38773 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38773
  have eq38787 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq38780
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38780
    | exact resolve eq38780 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq38780
  have eq38794 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq38787
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38787
    | exact resolve eq38787 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq38787
  have eq38801 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27531 eq38794
    | exact resolve eq38794 eq27531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27531 eq38794
  have eq38883 : (M.op (σ y) (σ (M.op x y))) = (k (σ (M.op x y)) (σ y)) := by grind
  have eq38901 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq38801 eq5834
    | exact resolve eq5834 eq38801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5834 eq38801
  have eq38914 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq27364 eq38901
    | exact resolve eq38901 eq27364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38901
  have eq38930 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq38766 eq38883
    | exact resolve eq38883 eq38766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38766 eq38883
  have eq38993 : (M.op (σ y) (σ (M.op x y))) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq38930 eq7313
    | exact resolve eq7313 eq38930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7313
  have eq39004 : (M.op (σ y) (σ (M.op x y))) = (M.op x (σ y)) := by
    first
    | exact superpose eq27364 eq38993
    | exact resolve eq38993 eq27364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27364 eq38993
  have eq39023 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq38930 eq39004
    | exact resolve eq39004 eq38930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38930 eq39004
  have eq39213 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq38914 eq28379
    | exact resolve eq28379 eq38914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28379 eq38914
  have eq39337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39023 eq39213
    | exact resolve eq39213 eq39023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39023 eq39213
  have eq39380 : False := by grind
  exact eq39380

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_pyy_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op X0 (M.op x y)))) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) X0 X0
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq77 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq44
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq44 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq119 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq112 eq77
    | (have j0 := eq77 (σ x) (σ y)
       grind)
    | exact resolve eq77 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq125
       have r₂ := eq27
       grind)
    | exact resolve eq125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130 eq27
    | exact resolve eq27 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq77 (σ X0) sF3
       grind)
    | exact superpose eq77 eq40
    | (have j1 := eq77 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq77
  have eq222 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq242 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq130 eq51
    | exact resolve eq51 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq251 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq242 eq14
    | exact resolve eq14 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq277 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq283 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq277 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq497 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130 eq120
    | (have r₁ := eq120
       have r₂ := eq130
       grind)
    | exact resolve eq120 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq130
  have eq498 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq497
  have eq1405 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq498 eq112
    | exact resolve eq112 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq1408 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq1405
  have eq1477 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1408 eq283
    | exact resolve eq283 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq1479 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq1477
    | exact resolve eq1477 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq1486 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1479 eq112
    | exact resolve eq112 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq1479
  have eq1489 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq1486
  have eq1493 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1489
       have r₂ := eq27
       grind)
    | exact resolve eq1489 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq1498 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1493 eq251
    | exact resolve eq251 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq1493
  have eq1536 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1498
  have eq1540 : y = (M.op x y) := by
    first
    | (have r₁ := eq1536
       have r₂ := eq132
       grind)
    | exact resolve eq1536 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq1536
  have eq1542 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1540 eq20
    | exact resolve eq20 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1547 : y ≠ y ∨ y = (M.op y x) ∨ (k x y) = (M.op y y) := by
    first
    | exact superpose eq1540 eq119
    | (have r₁ := eq119
       have r₂ := eq1540
       grind)
    | exact resolve eq119 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1552 : y = (M.op y y) := by
    first
    | exact superpose eq1540 eq222
    | exact resolve eq222 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq1556 : y = (M.op y x) ∨ (k x y) = (M.op y y) := by grind
  clear eq1547
  have eq1562 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1542
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1542
    | exact resolve eq1542 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq1563 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1562 eq26
    | exact resolve eq26 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2696 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq1562 eq198
    | (have j0 := eq198 X0
       grind)
    | exact resolve eq198 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq2697 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1562 eq2696
    | (have j0 := eq2696 X0
       grind)
    | exact resolve eq2696 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2696
  have eq2720 : (σ (k x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2697 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2697
    | (have j0 := eq2697 x
       grind)
    | exact resolve eq2697 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2697
  have eq2740 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1563 eq2720
    | exact resolve eq2720 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720
  have eq2757 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2740
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq2740
    | exact resolve eq2740 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2740
  have eq2768 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1562 eq2757
    | exact resolve eq2757 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757
  have eq2777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1563 eq2768
    | exact resolve eq2768 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563 eq2768
  have eq2783 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2777
       have r₂ := eq27
       grind)
    | exact resolve eq2777 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2777
  have eq2799 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2783 eq62
    | exact resolve eq62 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq2783
  have eq2801 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1540 eq2799
    | exact resolve eq2799 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2799
  have eq2897 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1556
       have i₂ := eq1552
       grind)
    | exact superpose eq1552 eq1556
    | exact resolve eq1556 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552 eq1556
  have eq2898 : y = (M.op y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2897
       have i₂ := eq2801
       grind)
    | exact superpose eq2801 eq2897
    | exact resolve eq2897 eq2801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2897
  have eq2909 : (M.op x y) = (k x y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq283 y x
       have i₂ := eq2898
       grind)
    | exact superpose eq2898 eq283
    | exact resolve eq283 eq2898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq2898
  have eq2911 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2909
       have i₂ := eq2801
       grind)
    | exact superpose eq2801 eq2909
    | exact resolve eq2909 eq2801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2801 eq2909
  have eq2915 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2911
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2911
    | exact resolve eq2911 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2911
  have eq2918 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1540 eq2915
    | exact resolve eq2915 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540 eq2915
  have eq2919 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq2918
  have eq2923 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2919 eq15
    | exact resolve eq15 eq2919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919
  have eq2934 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2923
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2923
    | exact resolve eq2923 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2923
  have eq2935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1562 eq2934
    | exact resolve eq2934 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562 eq2934
  have eq2936 : False := by grind
  exact eq2936

/-- `Equation4429`: `x ◇ (x ◇ y) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pyx_Equation4429 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4429 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4429.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq177 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq37 (M.op y y)
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq37
    | exact resolve eq37 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq182 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq179
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq179
    | exact resolve eq179 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq209 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq175
  have eq220 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq209
    | exact resolve eq209 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq690 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X4) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4 X5
       have i₂ := eq16 X2 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X2 X3 X4 (M.op X4 x)
       have i₂ := eq16 X4 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 X1 X4 : G, (M.op (M.op (M.op X0 X1) X0) X4) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq693 X0 X1 x x X4
       have i₂ := eq696 x x
       grind)
    | exact superpose eq696 eq693
    | exact resolve eq693 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq704 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq695 X0 (M.op X0 x)
       have i₂ := eq695 X0 x
       grind)
    | exact superpose eq695 eq695
    | exact resolve eq695 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq695 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq695
    | (have j0 := eq695 x y
       grind)
    | exact resolve eq695 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : (M.op (M.op x y) x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq695
    | (have j0 := eq695 (σ x) (σ y)
       grind)
    | exact resolve eq695 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op x y) x) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq695 x x
       grind)
    | exact superpose eq695 eq16
    | exact resolve eq16 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq695 x x
       have i₂ := eq696 x x
       grind)
    | exact superpose eq696 eq695
    | exact resolve eq695 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq767 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op X1 (k X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq695 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq695
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq695 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq774 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (k X0 X1) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq795 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq826 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (k X0 X1) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 X1 x x
       have i₂ := eq696 x x
       grind)
    | exact superpose eq696 eq774
    | (have j0 := eq774 X0 X1 x x
       grind)
    | exact resolve eq774 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq774
  have eq841 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (k X0 X1) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq735 eq826
    | (have j0 := eq826 X0 X1
       grind)
    | exact resolve eq826 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq850 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq796 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq796
    | (have j0 := eq796 (σ X0)
       grind)
    | exact resolve eq796 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq859 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) ∨ (M.op (M.op x y) x) = X0 ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq704 eq11
    | (have j0 := eq11 (M.op (M.op x y) x) X0
       grind)
    | exact resolve eq11 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq864 : ∀ X0 : G, (M.op (M.op x y) x) ≠ X0 ∨ (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq704 eq28
    | (have j0 := eq28 (M.op (M.op x y) x) X0
       grind)
    | (have r₁ := eq28 (M.op (M.op x y) x) (M.op (M.op x y) x)
       have r₂ := eq704 (M.op (M.op x y) x)
       grind)
    | exact resolve eq28 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq868 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | (have j0 := eq859 X0
       have j1 := eq864 X0
       grind)
    | (have r₁ := eq859 X0
       have r₂ := eq864 (k (M.op (M.op x y) x) X0)
       grind)
    | (have r₁ := eq859 X0
       have r₂ := eq864 X0
       grind)
    | (have r₁ := eq859 (M.op (M.op x y) x)
       have r₂ := eq864 (M.op (M.op x y) x)
       grind)
    | exact resolve eq859 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859 eq864
  have eq870 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | (have j0 := eq868 X0
       have j1 := eq13 (M.op (M.op x y) x) X0
       grind)
    | (have r₁ := eq868 x
       have r₂ := eq13 (M.op (M.op x y) x) x
       grind)
    | (have r₁ := eq868 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op (M.op x y) x) (M.op (M.op x y) x))
       grind)
    | exact resolve eq868 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq1099 : (σ (M.op (M.op x y) x)) = (k (σ (M.op (M.op x y) x)) (σ (M.op x y))) := by
    first
    | exact superpose eq870 eq42
    | exact resolve eq42 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1101 : (τ (M.op (M.op x y) x)) = (k (τ (M.op (M.op x y) x)) x) := by
    first
    | exact superpose eq870 eq142
    | exact resolve eq142 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3047 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq765
       grind)
    | exact superpose eq765 eq40
    | exact resolve eq40 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3049 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq3051 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq3049
    | exact resolve eq3049 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049
  have eq3255 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3051 eq767
    | exact resolve eq767 eq3051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3263 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq3255
       have r₂ := eq27
       grind)
    | exact resolve eq3255 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3255
  have eq3268 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3263 eq220
    | exact resolve eq220 eq3263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3263
  have eq3302 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq3268
    | exact resolve eq3268 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3268
  have eq3312 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq3302
       have r₂ := eq176
       grind)
    | exact resolve eq3302 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq3302
  have eq3316 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq3312
       have r₂ := eq13 y x
       grind)
    | exact resolve eq3312 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3312
  have eq3320 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq3316
       grind)
    | exact superpose eq3316 eq40
    | exact resolve eq40 eq3316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3316
  have eq3321 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3320
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3320
    | exact resolve eq3320 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320
  have eq3323 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq3321
       have r₂ := eq177
       grind)
    | exact resolve eq3321 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq3321
  have eq3327 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3323 eq3051
    | exact resolve eq3051 eq3323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3051
  have eq3328 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3323 eq767
    | exact resolve eq767 eq3323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq3331 : (τ (σ y)) = (k (τ (σ y)) x) := by
    first
    | exact superpose eq3323 eq142
    | exact resolve eq142 eq3323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq3332 : y = (k y x) := by
    first
    | exact superpose eq32 eq3331
    | exact resolve eq3331 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3331
  have eq3337 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq765
       have i₂ := eq3332
       grind)
    | exact superpose eq3332 eq765
    | exact resolve eq765 eq3332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq3347 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq3327
       grind)
    | exact superpose eq3327 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq3327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3349 : x ≠ y ∨ y = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq3327
       grind)
    | exact superpose eq3327 eq28
    | (have j0 := eq28 y y
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq3327
       grind)
    | exact resolve eq28 eq3327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3357 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq701 y y X0
       have i₂ := eq3327
       grind)
    | exact superpose eq3327 eq701
    | exact resolve eq701 eq3327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3360 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq710 y y
       have i₂ := eq3327
       grind)
    | exact superpose eq3327 eq710
    | exact resolve eq710 eq3327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327
  have eq3363 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3347
  have eq3366 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3360
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3360
    | exact resolve eq3360 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3360
  have eq3369 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq3357 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3357
    | (have j0 := eq3357 X0
       grind)
    | exact resolve eq3357 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357
  have eq3380 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq735 eq3369
    | exact resolve eq3369 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3369
  have eq3387 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq3366 eq3380
    | exact resolve eq3380 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3380
  have eq3390 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3328
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq3328
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq3328 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3394 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3328 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq3328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3397 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq3328 eq690
    | exact resolve eq690 eq3328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3407 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3328 eq710
    | exact resolve eq710 eq3328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328
  have eq3410 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3394
  have eq3411 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3390
  have eq3413 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3407
    | exact resolve eq3407 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3407
  have eq3422 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq26 eq3397
    | (have j0 := eq3397 X0 X1 X2
       grind)
    | exact resolve eq3397 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3397
  have eq3425 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3410 eq3411
    | exact resolve eq3411 eq3410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3410 eq3411
  have eq3432 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq3422 x x X2
       have i₂ := eq710 x x
       grind)
    | (have i₁ := eq3422 x y X2
       have i₂ := eq710 X2 x
       grind)
    | exact superpose eq710 eq3422
    | (have j0 := eq3422 x y X2
       grind)
    | exact resolve eq3422 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3422
  have eq3435 : ∀ X2 : G, (M.op (σ x) (σ y)) = (M.op X2 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq3413 eq3432
    | exact resolve eq3432 eq3413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3432
  have eq3577 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq710 y y
       have i₂ := eq3337
       grind)
    | exact superpose eq3337 eq710
    | exact resolve eq710 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3337
  have eq3583 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3577
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3577
    | exact resolve eq3577 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3577
  have eq3638 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3366 eq1099
    | exact resolve eq1099 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq3705 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq3638
    | exact resolve eq3638 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3638
  have eq4068 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3413 eq3387
    | exact resolve eq3387 eq3413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387
  have eq4768 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3705 eq794
    | (have j0 := eq794 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq794 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq3705
       grind)
    | exact resolve eq794 eq3705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3705
  have eq4769 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4768
  have eq4770 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4769
  have eq5354 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4770 eq701
    | exact resolve eq701 eq4770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5357 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4770 eq710
    | exact resolve eq710 eq4770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5363 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3366 eq5357
    | exact resolve eq5357 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5357
  have eq5366 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq735 eq5354
    | exact resolve eq5354 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5354
  have eq5379 : ∀ X0 : G, (M.op x y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq3366 eq5366
    | exact resolve eq5366 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5366
  have eq5387 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4770 eq5379
    | exact resolve eq5379 eq4770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5379
  have eq5449 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5363 eq4770
    | exact resolve eq4770 eq5363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4770 eq5363
  have eq5472 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq5449
  have eq5532 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  have eq8300 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq3363
       grind)
    | exact superpose eq3363 eq41
    | exact resolve eq41 eq3363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3363
  have eq8317 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq8300
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8300
    | exact resolve eq8300 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8300
  have eq8319 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq8317
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8317
    | exact resolve eq8317 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8317
  have eq8592 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8319 eq841
    | (have j0 := eq841 (σ y) (σ y)
       grind)
    | exact resolve eq841 eq8319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8319
  have eq8596 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq8592
  have eq8597 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq8596
    | exact resolve eq8596 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8596
  have eq8601 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3366 eq8597
    | exact resolve eq8597 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8597
  have eq10592 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4068 eq708
    | exact resolve eq708 eq4068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4068
  have eq10608 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10592
    | exact resolve eq10592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10592
  have eq10610 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3366 eq10608
    | exact resolve eq10608 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3366 eq10608
  have eq10611 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq10610
  have eq13377 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3425 eq116
    | exact resolve eq116 eq3425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq3425
  have eq13395 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq13377
    | exact resolve eq13377 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13377
  have eq14176 : (M.op (σ x) (σ x)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq13395 eq710
    | exact resolve eq710 eq13395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14182 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq3413 eq14176
    | exact resolve eq14176 eq3413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14176
  have eq14201 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq13395 eq14182
    | exact resolve eq14182 eq13395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13395 eq14182
  have eq14202 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14201
  have eq14223 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq14202
       grind)
    | exact superpose eq14202 eq41
    | exact resolve eq41 eq14202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq14227 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq841 y y
       have i₂ := eq14202
       grind)
    | exact superpose eq14202 eq841
    | (have j0 := eq841 y y
       grind)
    | exact resolve eq841 eq14202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14231 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14227
  have eq14232 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14231
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14231
    | exact resolve eq14231 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14231
  have eq14233 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14223
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14223
    | exact resolve eq14223 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14223
  have eq14239 : y = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3413 eq14232
    | exact resolve eq14232 eq3413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14232
  have eq14240 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14233
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14233
    | exact resolve eq14233 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14233
  have eq14275 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq182
       have i₂ := eq14239
       grind)
    | exact superpose eq14239 eq182
    | exact resolve eq182 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq14279 : y ≠ y ∨ y = (k y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq14239
       grind)
    | exact superpose eq14239 eq28
    | (have j0 := eq28 y y
       grind)
    | (have r₁ := eq28 y y
       have r₂ := eq14239
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq14239
       grind)
    | exact resolve eq28 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14289 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op y y) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq701 y y X0
       have i₂ := eq14239
       grind)
    | exact superpose eq14239 eq701
    | exact resolve eq701 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14292 : (M.op y y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq710 y y
       have i₂ := eq14239
       grind)
    | exact superpose eq14239 eq710
    | exact resolve eq710 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14295 : y = (k y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14279
  have eq14302 : y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14239 eq14292
    | exact resolve eq14292 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14292
  have eq14305 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op y y) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq735 eq14289
    | exact resolve eq14289 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14289
  have eq14315 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14202 eq14295
    | exact resolve eq14295 eq14202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14202 eq14295
  have eq14318 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14275
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14275
    | exact resolve eq14275 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14275
  have eq14321 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op y X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14239 eq14305
    | exact resolve eq14305 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14239 eq14305
  have eq14329 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14240 eq14318
    | exact resolve eq14318 eq14240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14240 eq14318
  have eq14331 : ∀ X0 : G, y = (M.op y X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14302 eq14321
    | exact resolve eq14321 eq14302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14321
  have eq14336 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14315 eq14331
    | exact resolve eq14331 eq14315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14331
  have eq14423 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14329 eq27
    | exact resolve eq27 eq14329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14435 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14329 eq10611
    | exact resolve eq10611 eq14329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10611
  have eq14449 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14329
  have eq14464 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14435
  have eq14474 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14464
       have r₂ := eq14449
       grind)
    | exact resolve eq14464 eq14449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14464
  have eq14481 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14474
       have r₂ := eq14423
       grind)
    | exact resolve eq14474 eq14423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14423 eq14474
  have eq14623 : y = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14302 eq3413
    | exact resolve eq3413 eq14302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14302
  have eq14653 : y = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq14623
  have eq14680 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14315 eq14653
    | exact resolve eq14653 eq14315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14315 eq14653
  have eq14821 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14680 eq708
    | exact resolve eq708 eq14680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq14845 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  have eq14855 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14821
    | exact resolve eq14821 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14821
  have eq14860 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3413 eq14855
    | exact resolve eq14855 eq3413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3413 eq14855
  have eq14907 : x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14336 y
       grind)
    | exact superpose eq14336 eq18
    | (have j1 := eq14336 y
       grind)
    | exact resolve eq18 eq14336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14336
  have eq14993 : x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14481 eq14907
    | exact resolve eq14907 eq14481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14481 eq14907
  have eq14994 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14993
  have eq16353 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14860 eq870
    | exact resolve eq870 eq14860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14860
  have eq16518 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14994 eq16353
    | (have j0 := eq16353 X0
       grind)
    | exact resolve eq16353 eq14994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16353
  have eq18621 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14680 eq16518
    | exact resolve eq16518 eq14680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14680 eq16518
  have eq18642 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18621 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18621
  have eq18653 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18642 X0
       grind)
    | (have r₁ := eq18642 X0
       have r₂ := eq14449
       grind)
    | exact resolve eq18642 eq14449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14449 eq18642
  have eq18663 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18653 X0
       grind)
    | (have r₁ := eq18653 X0
       have r₂ := eq14845
       grind)
    | exact resolve eq18653 eq14845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14845 eq18653
  have eq18669 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14994 eq18663
    | (have j0 := eq18663 X0
       grind)
    | exact resolve eq18663 eq14994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18663
  have eq18670 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18669 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18669
  have eq18705 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18670 eq796
    | (have j0 := eq796 (σ y)
       grind)
    | (have r₁ := eq796 (σ y)
       have r₂ := eq18670 (σ y)
       grind)
    | exact resolve eq796 eq18670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq18717 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18670 eq153
    | exact resolve eq153 eq18670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq18670
  have eq18718 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq18705
  have eq18727 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq18717
    | exact resolve eq18717 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18717
  have eq18778 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ y) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18718 eq701
    | exact resolve eq701 eq18718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18781 : (M.op (σ y) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18718 eq710
    | exact resolve eq710 eq18718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18791 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14994 eq18781
    | exact resolve eq18781 eq14994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18781
  have eq18794 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (σ y) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq735 eq18778
    | exact resolve eq18778 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18778
  have eq18806 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18718 eq18791
    | exact resolve eq18791 eq18718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18791
  have eq18807 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ y) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14994 eq18794
    | exact resolve eq18794 eq14994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18794
  have eq18817 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18718 eq18807
    | exact resolve eq18807 eq18718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18718 eq18807
  have eq18825 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18806 eq18817
    | exact resolve eq18817 eq18806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18817
  have eq18855 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq794 y y
       have i₂ := eq18727
       grind)
    | exact superpose eq18727 eq794
    | (have j0 := eq794 y y
       grind)
    | (have r₁ := eq794 y y
       have r₂ := eq18727
       grind)
    | exact resolve eq794 eq18727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18727
  have eq18856 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq18855
  have eq18857 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq18856
  have eq19117 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18825 eq3435
    | exact resolve eq3435 eq18825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3435 eq18825
  have eq19118 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq19117
  have eq19254 : (M.op x y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq19118
  have eq20402 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq690 y y X2 X0 X1
       have i₂ := eq18857
       grind)
    | exact superpose eq18857 eq690
    | exact resolve eq690 eq18857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq20436 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq20402 x x X2
       have i₂ := eq710 x x
       grind)
    | (have i₁ := eq20402 x y X2
       have i₂ := eq710 X2 x
       grind)
    | exact superpose eq710 eq20402
    | (have j0 := eq20402 x y X2
       grind)
    | exact resolve eq20402 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20402
  have eq20449 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq14994 eq20436
    | exact resolve eq20436 eq14994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14994 eq20436
  have eq20458 : ∀ X2 : G, (σ y) = (M.op X2 (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq18806 eq20449
    | exact resolve eq20449 eq18806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18806 eq20449
  have eq20463 : ∀ X2 : G, (σ y) = (M.op X2 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq18857 eq20458
    | exact resolve eq20458 eq18857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18857 eq20458
  have eq20928 : (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20463 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq20463 x
       grind)
    | exact superpose eq20463 eq18
    | (have j1 := eq20463 x
       grind)
    | exact resolve eq18 eq20463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20463
  have eq20962 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20928
       have r₂ := eq19254
       grind)
    | exact resolve eq20928 eq19254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19254 eq20928
  have eq21022 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20962 eq27
    | exact resolve eq27 eq20962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21028 : (M.op (σ x) (σ x)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20962 eq735
    | exact resolve eq735 eq20962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21033 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  have eq21061 : (k (σ x) (σ x)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21028 eq11
    | exact resolve eq11 eq21028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21028
  have eq21079 : (k (σ x) (σ x)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq21061
  have eq24867 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq773 y x
       have i₂ := eq3332
       grind)
    | exact superpose eq3332 eq773
    | (have j0 := eq773 y x
       grind)
    | exact resolve eq773 eq3332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3332
  have eq24964 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3323 eq773
    | (have j0 := eq773 (σ y) (σ x)
       grind)
    | exact resolve eq773 eq3323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq3323
  have eq25098 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq24964
    | exact resolve eq24964 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24964
  have eq25129 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq24867
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24867
    | exact resolve eq24867 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24867
  have eq25215 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq25098
    | exact resolve eq25098 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25098
  have eq25237 : x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25129
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25129
    | exact resolve eq25129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25129
  have eq25301 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20962 eq25215
    | exact resolve eq25215 eq20962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25215
  have eq25321 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3583 eq25237
    | exact resolve eq25237 eq3583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3583 eq25237
  have eq25557 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25301 eq710
    | exact resolve eq710 eq25301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25301
  have eq25577 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq25557
    | exact resolve eq25557 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25557
  have eq25593 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20962 eq25577
    | exact resolve eq25577 eq20962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20962 eq25577
  have eq25594 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25593
  have eq25621 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq25594 eq870
    | exact resolve eq870 eq25594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26238 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25621 eq850
    | (have j0 := eq850 (M.op x y)
       grind)
    | exact resolve eq850 eq25621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25621
  have eq26260 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26238
  have eq26274 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq26260
    | exact resolve eq26260 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26260
  have eq26599 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq5472 eq26274
    | exact resolve eq26274 eq5472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26630 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26274 eq710
    | exact resolve eq710 eq26274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26636 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25594 eq26630
    | exact resolve eq26630 eq25594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25594 eq26630
  have eq26676 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26636 eq26274
    | exact resolve eq26274 eq26636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26274 eq26636
  have eq26698 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq26676
  have eq26739 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26698 eq27
    | exact resolve eq27 eq26698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26698
  have eq26755 : (σ x) ≠ (σ y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq5472 eq26739
    | exact resolve eq26739 eq5472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26756 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq26755
       have r₂ := eq5532
       grind)
    | exact resolve eq26755 eq5532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5532 eq26755
  have eq30521 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq25321 eq870
    | exact resolve eq870 eq25321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq31193 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30521 eq850
    | (have j0 := eq850 (M.op x y)
       grind)
    | exact resolve eq850 eq30521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq30521
  have eq31216 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq31193
  have eq31229 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq31216
    | exact resolve eq31216 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31216
  have eq34609 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31229 eq710
    | exact resolve eq710 eq31229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34631 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq25321 eq34609
    | exact resolve eq34609 eq25321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25321 eq34609
  have eq34883 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq34631 eq31229
    | exact resolve eq31229 eq34631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31229 eq34631
  have eq34907 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq34883
  have eq34990 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq34907 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq34907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34907
  have eq35009 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq34990
  have eq35080 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq35009 eq42
    | exact resolve eq42 eq35009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq35009
  have eq35118 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq35080
    | exact resolve eq35080 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35080
  have eq35125 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq35118
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35118
    | exact resolve eq35118 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35118
  have eq35128 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq5472 eq35125
    | exact resolve eq35125 eq5472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5472 eq35125
  have eq35162 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq35128 eq841
    | (have j0 := eq841 (σ y) (σ y)
       grind)
    | exact resolve eq841 eq35128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq35166 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq35162
  have eq35179 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26 eq35166
    | exact resolve eq35166 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35166
  have eq35189 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26599 eq35179
    | exact resolve eq35179 eq26599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26599 eq35179
  have eq60074 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq35189 eq28
    | (have j0 := eq28 (σ y) (σ y)
       grind)
    | (have r₁ := eq28 (σ y) (σ y)
       have r₂ := eq35189
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq35189
       grind)
    | exact resolve eq28 eq35189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq35189
  have eq60096 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq60074
  have eq60115 : (σ x) = (σ y) ∨ (σ x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq35128 eq60096
    | exact resolve eq60096 eq35128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35128 eq60096
  have eq60135 : (σ x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq60115
       have r₂ := eq26756
       grind)
    | exact resolve eq60115 eq26756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26756 eq60115
  have eq60211 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq60135 eq1101
    | exact resolve eq1101 eq60135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq60367 : x = (k x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq30 eq60211
    | exact resolve eq60211 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60211
  have eq61469 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq794 x x
       have i₂ := eq60367
       grind)
    | exact superpose eq60367 eq794
    | (have j0 := eq794 x x
       grind)
    | (have r₁ := eq794 x x
       have r₂ := eq60367
       grind)
    | exact resolve eq794 eq60367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq60367
  have eq61485 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq61469
  have eq61486 : x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq61485
  have eq61953 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op x x) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq701 x x X0
       have i₂ := eq61486
       grind)
    | exact superpose eq61486 eq701
    | exact resolve eq701 eq61486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq61956 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq710 x x
       have i₂ := eq61486
       grind)
    | exact superpose eq61486 eq710
    | exact resolve eq710 eq61486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61968 : (σ x) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq60135 eq61956
    | exact resolve eq61956 eq60135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61956
  have eq61971 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x x) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq735 eq61953
    | exact resolve eq61953 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq61953
  have eq61984 : ∀ X0 : G, (σ x) = (M.op (M.op x x) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq60135 eq61971
    | exact resolve eq61971 eq60135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60135 eq61971
  have eq61992 : ∀ X0 : G, (σ x) = (M.op x X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq61486 eq61984
    | exact resolve eq61984 eq61486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61984
  have eq62001 : x = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq61486
       have i₂ := eq61968
       grind)
    | exact superpose eq61968 eq61486
    | exact resolve eq61486 eq61968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61486 eq61968
  have eq62032 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq62001
  have eq62509 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq61992 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq61992 x
       grind)
    | exact superpose eq61992 eq18
    | (have j1 := eq61992 y
       grind)
    | exact resolve eq18 eq61992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61992
  have eq62697 : x = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq62509 eq30
    | exact resolve eq30 eq62509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq62794 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq62509 eq21033
    | (have r₁ := eq21033
       have r₂ := eq62509
       grind)
    | exact resolve eq21033 eq62509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62844 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq62794
  have eq62928 : (σ x) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq62032 eq62697
    | exact resolve eq62697 eq62032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62032 eq62697
  have eq62953 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq62509 eq62928
    | exact resolve eq62928 eq62509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62509 eq62928
  have eq63181 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq62953 eq14
    | exact resolve eq14 eq62953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62953
  have eq63243 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq63181
    | exact resolve eq63181 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63181
  have eq63244 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq63243
  have eq63255 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63244 eq29
    | exact resolve eq29 eq63244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq63308 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq63244 eq5387
    | exact resolve eq5387 eq63244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5387
  have eq63438 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have j0 := eq63308 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63308
  have eq65354 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq63438 eq21079
    | exact resolve eq21079 eq63438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21079
  have eq65545 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq65354
       have r₂ := eq21033
       grind)
    | exact resolve eq65354 eq21033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21033 eq65354
  have eq72196 : (k x x) = (τ (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq65545 eq98
    | exact resolve eq98 eq65545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq65545
  have eq72265 : (M.op x y) = (k x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq63255 eq72196
    | exact resolve eq72196 eq63255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72196
  have eq85427 : y = (k y (τ (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8601 eq220
    | exact resolve eq220 eq8601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq85450 : (M.op (σ y) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8601 eq710
    | exact resolve eq710 eq8601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq85467 : (σ y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8601 eq85450
    | exact resolve eq85450 eq8601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8601 eq85450
  have eq85486 : y = (k y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32 eq85427
    | exact resolve eq85427 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85427
  have eq85492 : (σ y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq62844 eq85467
    | exact resolve eq85467 eq62844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85467
  have eq85505 : y = (k y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq85486
       have r₂ := eq3349
       grind)
    | exact resolve eq85486 eq3349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349 eq85486
  have eq85509 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq63438 eq85492
    | exact resolve eq85492 eq63438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63438 eq85492
  have eq85510 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq85509
  have eq85521 : y = (k y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq62844 eq85505
    | exact resolve eq85505 eq62844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62844 eq85505
  have eq85527 : x = (k x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq85510 eq85521
    | exact resolve eq85521 eq85510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85510 eq85521
  have eq85528 : x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq72265 eq85527
    | exact resolve eq85527 eq72265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72265 eq85527
  have eq85529 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq85528
  have eq85546 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq85529 eq27
    | exact resolve eq27 eq85529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85529
  have eq85773 : (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq85546
       have r₂ := eq63244
       grind)
    | exact resolve eq85546 eq63244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85546
  have eq85809 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq85773 eq26
    | exact resolve eq26 eq85773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq85810 : y = (τ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq85773 eq32
    | exact resolve eq32 eq85773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq85773
  have eq86068 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63255 eq85810
    | exact resolve eq85810 eq63255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63255 eq85810
  have eq86090 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq86068
       grind)
    | exact superpose eq86068 eq18
    | exact resolve eq18 eq86068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq86068
  have eq86184 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq707 eq86090
    | exact resolve eq86090 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq86090
  have eq86436 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq86184 eq704
    | exact resolve eq704 eq86184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704 eq86184
  have eq86911 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq86436 eq85809
    | exact resolve eq85809 eq86436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85809 eq86436
  have eq86940 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq86911
  have eq87081 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq86940 eq27
    | exact resolve eq27 eq86940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86940
  have eq87230 : x = (M.op x y) := by
    first
    | (have r₁ := eq87081
       have r₂ := eq63244
       grind)
    | exact resolve eq87081 eq63244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63244 eq87081
  have eq87242 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq87230
       grind)
    | exact superpose eq87230 eq22
    | exact resolve eq22 eq87230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq87230
  have eq87369 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq87242 eq20
    | exact resolve eq20 eq87242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq87242
  have eq87600 : (σ x) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87369 eq21022
    | (have r₁ := eq21022
       have r₂ := eq87369
       grind)
    | exact resolve eq21022 eq87369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21022
  have eq87638 : (σ x) ≠ (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq87369 eq26739
    | (have r₁ := eq26739
       have r₂ := eq87369
       grind)
    | exact resolve eq26739 eq87369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26739
  have eq87669 : (M.op x y) = (σ x) := by grind
  clear eq87638
  have eq87673 : (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq87600
  have eq88045 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq87673 eq27
    | exact resolve eq27 eq87673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq87673
  have eq88148 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq87369 eq88045
    | exact resolve eq88045 eq87369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87369 eq88045
  have eq88154 : False := by grind
  exact eq88154

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq291 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq90 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq294 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq291 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq295 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq294 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq297 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq295
    | (have j0 := eq295 X0 X1
       grind)
    | exact resolve eq295 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq301 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq297 X0 X1
       have j1 := eq293 X1 X0
       grind)
    | (have r₁ := eq297 X1 X0
       have r₂ := eq293 X0 X1
       grind)
    | (have r₁ := eq297 (k X1 X0) X1
       have r₂ := eq293 X0 X1
       grind)
    | (have r₁ := eq297 X1 X1
       have r₂ := eq293 X1 X1
       grind)
    | exact resolve eq297 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq297
  have eq613 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq301 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq301
    | exact resolve eq301 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq301 y x
       grind)
    | exact superpose eq301 eq16
    | (have j1 := eq301 y x
       grind)
    | exact resolve eq16 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq643 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq613
    | (have j0 := eq613 X0 X1
       grind)
    | exact resolve eq613 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq613
  have eq644 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq643 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq643
    | exact resolve eq643 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq707 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq644 (τ X1) X0
       grind)
    | exact superpose eq644 eq18
    | (have j1 := eq644 (τ X1) X0
       grind)
    | exact resolve eq18 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq644
  have eq905 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq707 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq707
    | exact resolve eq707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq956 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq905 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq905
    | (have j0 := eq905 X0 X1
       grind)
    | exact resolve eq905 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq1062 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq627
       have i₂ := eq956 y x
       grind)
    | exact superpose eq956 eq627
    | (have j1 := eq956 (σ y) (σ x)
       grind)
    | (have r₁ := eq627
       have r₂ := eq956 y x
       grind)
    | exact resolve eq627 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1063 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1062
  have eq1107 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1063
  have eq1116 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq627
       have i₂ := eq1107
       grind)
    | exact superpose eq1107 eq627
    | exact resolve eq627 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627 eq1107
  have eq1117 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1116
  have eq1118 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1117
  have eq1189 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1118
  have eq1200 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1189
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1189
    | exact resolve eq1189 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1205 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1200
       grind)
    | exact superpose eq1200 eq16
    | exact resolve eq16 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1285 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1205
       have i₂ := eq956 y x
       grind)
    | exact superpose eq956 eq1205
    | (have j1 := eq956 y x
       grind)
    | (have r₁ := eq1205
       have r₂ := eq956 y x
       grind)
    | exact resolve eq1205 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq1286 : y = (M.op x x) := by grind
  clear eq1285
  have eq1291 : (M.op x y) = (k y x) := by grind
  clear eq1286
  have eq1344 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1205
       have i₂ := eq1291
       grind)
    | exact superpose eq1291 eq1205
    | exact resolve eq1205 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq1291
  have eq1347 : False := by grind
  exact eq1347

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_x_pxy_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) ≠ (M.op X0 (M.op X0 (M.op X1 X0))) ∨ (k X2 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op X2 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op X0 (M.op X1 X0)))
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X1 (M.op X2 X1)))
       have r₂ := eq9 (M.op X1 (M.op X1 (M.op X2 X1))) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op X2 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq65 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X0 (M.op X1 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq68 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X1 (M.op X2 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (M.op X1 (M.op X1 (M.op X2 X1)))
       have i₂ := eq65 X1 X2 (σ X0)
       grind)
    | exact superpose eq65 eq28
    | exact resolve eq28 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq71 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X1 (M.op X2 X1))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68
    | exact resolve eq68 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq773 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
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
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq773 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq1268 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq814 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq1269 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1369 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1269 (σ X0) (σ X1)
       grind)
    | exact superpose eq1269 eq15
    | (have j1 := eq1269 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1377 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1269 (τ X0) X1
       grind)
    | exact superpose eq1269 eq17
    | (have j1 := eq1269 (τ X0) X1
       grind)
    | exact resolve eq17 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269
  have eq1459 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1377 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1377
    | exact resolve eq1377 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq1504 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1459 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1459
    | (have j0 := eq1459 X0 X1
       grind)
    | exact resolve eq1459 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459
  have eq1647 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1369 x y
       grind)
    | exact superpose eq1369 eq16
    | (have j1 := eq1369 x y
       grind)
    | exact resolve eq16 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1677 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1369 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1711 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1677 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1677
    | (have j0 := eq1677 (τ X0) (τ X1)
       grind)
    | exact resolve eq1677 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1677
  have eq1719 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1711 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1711
    | (have j0 := eq1711 X0 X1
       grind)
    | exact resolve eq1711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1711
  have eq1731 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1719 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1719
    | (have j0 := eq1719 X0 X1
       grind)
    | exact resolve eq1719 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq1742 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1731 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1731
    | (have j0 := eq1731 X0 X1
       grind)
    | exact resolve eq1731 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731
  have eq1745 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1742 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1742
    | (have j0 := eq1742 X0 X1
       grind)
    | exact resolve eq1742 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742
  have eq1943 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1647
       have i₂ := eq1504 x y
       grind)
    | exact superpose eq1504 eq1647
    | (have j1 := eq1504 (σ x) (σ y)
       grind)
    | (have r₁ := eq1647
       have r₂ := eq1504 x y
       grind)
    | exact resolve eq1647 eq1504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq1944 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1943
  have eq1951 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq1944
       grind)
    | exact superpose eq1944 eq9
    | exact resolve eq9 eq1944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq1980 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq1951 (σ y)
       grind)
    | exact superpose eq1951 eq9
    | exact resolve eq9 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1981 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq65 (σ y) (σ y) X0
       have i₂ := eq1951 (σ y)
       grind)
    | exact superpose eq1951 eq65
    | exact resolve eq65 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1983 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq71 X0 (σ y) (σ y)
       have i₂ := eq1951 (σ y)
       grind)
    | exact superpose eq1951 eq71
    | exact resolve eq71 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1951
  have eq2065 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1983 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1983
    | exact resolve eq1983 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983
  have eq2077 : ∀ X0 : G, y ≠ X0 ∨ y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1745 X0 y
       have i₂ := eq2065 X0
       grind)
    | exact superpose eq2065 eq1745
    | (have j0 := eq1745 X0 y
       grind)
    | (have r₁ := eq1745 y y
       have r₂ := eq2065 y
       grind)
    | exact resolve eq1745 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745 eq2065
  have eq2127 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1980 (σ x)
       grind)
    | exact superpose eq1980 eq16
    | exact resolve eq16 eq1980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980
  have eq2187 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq1981 (σ X0)
       grind)
    | exact superpose eq1981 eq15
    | exact resolve eq15 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981
  have eq2509 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq2077 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq2510 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq2509
       grind)
    | exact superpose eq2509 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq2509
       grind)
    | exact resolve eq12 eq2509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509
  have eq2535 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2510 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2510
  have eq2538 : ∀ X0 : G, (σ X0) = (σ (M.op X0 y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2187 X0
       have i₂ := eq2535 X0
       grind)
    | exact superpose eq2535 eq2187
    | exact resolve eq2187 eq2535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187 eq2535
  have eq2555 : ∀ X0 : G, (σ X0) = (σ (M.op X0 y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538
  have eq2617 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2127
       have i₂ := eq2555 x
       grind)
    | exact superpose eq2555 eq2127
    | (have r₁ := eq2127
       have r₂ := eq2555 x
       grind)
    | exact resolve eq2127 eq2555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2555
  have eq2644 : (σ x) ≠ (σ x) ∨ y = (M.op x y) := by grind
  clear eq2617
  have eq2645 : y = (M.op x y) := by grind
  clear eq2644
  have eq2664 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq2645
       grind)
    | exact superpose eq2645 eq9
    | exact resolve eq9 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2645
  have eq2692 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq2664 y
       grind)
    | exact superpose eq2664 eq9
    | exact resolve eq9 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2693 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 y y X0
       have i₂ := eq2664 y
       grind)
    | exact superpose eq2664 eq65
    | exact resolve eq65 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq2664
  have eq2805 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2127
       have i₂ := eq2692 x
       grind)
    | exact superpose eq2692 eq2127
    | exact resolve eq2127 eq2692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq2809 : x = y := by grind
  clear eq2805
  have eq2839 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2809
       grind)
    | exact superpose eq2809 eq16
    | exact resolve eq16 eq2809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2864 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq2692 X0
       have i₂ := eq2809
       grind)
    | exact superpose eq2809 eq2692
    | exact resolve eq2692 eq2809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2868 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2839
       have i₂ := eq2864 x
       grind)
    | exact superpose eq2864 eq2839
    | exact resolve eq2839 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839 eq2864
  have eq2869 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq2693 X0
       have i₂ := eq2809
       grind)
    | exact superpose eq2809 eq2693
    | exact resolve eq2693 eq2809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2894 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1647
       have i₂ := eq2693 x
       grind)
    | exact superpose eq2693 eq1647
    | exact resolve eq1647 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647 eq2693
  have eq2895 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2894
       have i₂ := eq2692 x
       grind)
    | exact superpose eq2692 eq2894
    | exact resolve eq2894 eq2692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2692 eq2894
  have eq2896 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2895
  have eq2909 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2896
       have i₂ := eq2809
       grind)
    | exact superpose eq2809 eq2896
    | exact resolve eq2896 eq2809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2809 eq2896
  have eq2967 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 x
       have i₂ := eq2869 (τ X0)
       grind)
    | exact superpose eq2869 eq17
    | exact resolve eq17 eq2869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2869
  have eq2972 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2967 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2967
    | exact resolve eq2967 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2967
  have eq3686 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq2909
       grind)
    | exact superpose eq2909 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq2909
       grind)
    | exact resolve eq12 eq2909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2909
  have eq3711 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq3686 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3686
  have eq3736 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3711 X0
       have i₂ := eq2972 X0
       grind)
    | exact superpose eq2972 eq3711
    | exact resolve eq3711 eq2972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2972 eq3711
  have eq3809 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2868
       have i₂ := eq3736 (σ x)
       grind)
    | exact superpose eq3736 eq2868
    | (have r₁ := eq2868
       have r₂ := eq3736 (σ x)
       grind)
    | exact resolve eq2868 eq3736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2868 eq3736
  have eq3812 : False := by grind
  exact eq3812
