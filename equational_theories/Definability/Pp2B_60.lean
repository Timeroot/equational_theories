import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3947`: `x ◇ y = (x ◇ (z ◇ w)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pxy_pyx_Equation3947 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3947 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3947.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X2 X3)) X1) := by
    intro X0 X1 X2 X3
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  clear eq18
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq250 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq250 X0 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | (have r₁ := eq250 (k X0 X1) (M.op X1 X0) X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq250 (M.op X1 X0) (k X0 X1) X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq250 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq250 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq368 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq418 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq368 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq419 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq418 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq467 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq419 (σ X0)
       grind)
    | exact superpose eq419 eq15
    | exact resolve eq15 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq419 (τ X0)
       grind)
    | exact superpose eq419 eq32
    | exact resolve eq32 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq484 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq469 X0
       have i₂ := eq419 X0
       grind)
    | exact superpose eq419 eq469
    | exact resolve eq469 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq486 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq467 X0
       have i₂ := eq419 X0
       grind)
    | exact superpose eq419 eq467
    | exact resolve eq467 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq467
  have eq559 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op X1 X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq484 X0
       grind)
    | exact superpose eq484 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq484 X0
       grind)
    | exact superpose eq484 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq561 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq559 X0 X1
       have j1 := eq560 X0 X1
       grind)
    | (have r₁ := eq559 X0 X1
       have r₂ := eq560 X0 X1
       grind)
    | exact resolve eq559 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq560
  have eq576 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 (σ (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (σ X0) (σ X0)
       have i₂ := eq486 X0
       grind)
    | exact superpose eq486 eq9
    | exact resolve eq9 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq486 X0
       grind)
    | exact superpose eq486 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq486 X0
       grind)
    | exact superpose eq486 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 : G, (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq578 X0 X1
       have j1 := eq579 X0 X1
       grind)
    | (have r₁ := eq578 X0 X1
       have r₂ := eq579 X0 X1
       grind)
    | exact resolve eq578 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq902 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq561 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq561
    | exact resolve eq561 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq1578 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq580 X1 X0
       grind)
    | exact superpose eq580 eq10
    | (have j1 := eq580 X1 X0
       grind)
    | exact resolve eq10 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq2232 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1578 (σ X1) X0
       grind)
    | exact superpose eq1578 eq15
    | (have j1 := eq1578 (σ X1) X0
       grind)
    | exact resolve eq15 eq1578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq2247 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2232 X0 X1
       have i₂ := eq486 X1
       grind)
    | exact superpose eq486 eq2232
    | (have j0 := eq2232 X0 X1
       grind)
    | exact resolve eq2232 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232
  have eq2254 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2247 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq2247
    | (have j0 := eq2247 X0 X1
       grind)
    | exact resolve eq2247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247
  have eq2996 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2254 X0 X1
       have i₂ := eq902 X0 X1
       grind)
    | exact superpose eq902 eq2254
    | (have j0 := eq2254 X0 X1
       have j1 := eq902 X0 X1
       grind)
    | exact resolve eq2254 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902 eq2254
  have eq3099 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2996 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996
  have eq3855 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3099 x y
       grind)
    | exact superpose eq3099 eq16
    | (have j1 := eq3099 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3099 x y
       grind)
    | exact resolve eq16 eq3099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3959 : x = (M.op y y) := by grind
  clear eq3855
  have eq4028 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (σ x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq576 y X0 X1
       have i₂ := eq3959
       grind)
    | exact superpose eq3959 eq576
    | exact resolve eq576 eq3959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq4044 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq3099 X0 y
       have i₂ := eq3959
       grind)
    | exact superpose eq3959 eq3099
    | (have j0 := eq3099 X0 y
       grind)
    | exact resolve eq3099 eq3959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3099
  have eq4050 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 y y
       have i₂ := eq3959
       grind)
    | exact superpose eq3959 eq9
    | exact resolve eq9 eq3959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3959
  have eq4307 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq4028 (σ x) X0
       have i₂ := eq486 x
       grind)
    | exact superpose eq486 eq4028
    | exact resolve eq4028 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486 eq4028
  have eq6213 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x x) y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4307 (σ y)
       have i₂ := eq4044 (M.op x x)
       grind)
    | exact superpose eq4044 eq4307
    | (have j1 := eq4044 (M.op x x)
       grind)
    | exact resolve eq4307 eq4044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4044 eq4307
  have eq6260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6213
       have i₂ := eq4050 x y
       grind)
    | exact superpose eq4050 eq6213
    | exact resolve eq6213 eq4050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4050 eq6213
  have eq6269 : x = (M.op x x) := by
    first
    | (have r₁ := eq6260
       have r₂ := eq16
       grind)
    | exact resolve eq6260 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6260
  have eq6397 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq6269
       grind)
    | exact superpose eq6269 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq6269
       grind)
    | exact resolve eq12 eq6269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6426 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq6397 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6397
  have eq40124 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq579 x X0
       have i₂ := eq6269
       grind)
    | exact superpose eq6269 eq579
    | (have j0 := eq579 x X0
       grind)
    | exact resolve eq579 eq6269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq6269
  have eq40143 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq40124 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40124
  have eq41488 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq40143 (σ X0)
       grind)
    | exact superpose eq40143 eq15
    | exact resolve eq15 eq40143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40143
  have eq41523 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq41488 X0
       have i₂ := eq6426 X0
       grind)
    | exact superpose eq6426 eq41488
    | exact resolve eq41488 eq6426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6426 eq41488
  have eq41559 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41523 y
       grind)
    | exact superpose eq41523 eq16
    | (have r₁ := eq16
       have r₂ := eq41523 y
       grind)
    | exact resolve eq16 eq41523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41523
  have eq41566 : False := by grind
  exact eq41566

/-- `Equation3997`: `x ◇ y = (z ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation3997 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3997 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3997.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq42 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq97 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq208 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96 x y
       grind)
    | exact superpose eq96 eq16
    | (have j1 := eq96 x y
       grind)
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1176 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq214 (τ X1) (τ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq214
    | (have j0 := eq214 (τ X1) (τ X0)
       grind)
    | exact resolve eq214 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1193 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1176 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1176
    | (have j0 := eq1176 X0 X1
       grind)
    | exact resolve eq1176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1200 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1193 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1193
    | (have j0 := eq1193 X0 X1
       grind)
    | exact resolve eq1193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq1206 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1200 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1200
    | (have j0 := eq1200 X0 X1
       grind)
    | exact resolve eq1200 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1211 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1206 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1206
    | (have j0 := eq1206 X0 X1
       grind)
    | exact resolve eq1206 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1216 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1211 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1211
    | (have j0 := eq1211 X0 X1
       grind)
    | exact resolve eq1211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1219 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1216 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1216
    | (have j0 := eq1216 X0 X1
       grind)
    | exact resolve eq1216 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq4748 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq97 (σ X1) X1
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4774 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq97 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq4775 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4774 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4774
  have eq4776 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4748 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4748
  have eq4777 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4776 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4776
  have eq4779 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4775 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4775
    | (have j0 := eq4775 X0
       grind)
    | exact resolve eq4775 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4775
  have eq4825 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq4779 X0
       grind)
    | exact superpose eq4779 eq42
    | (have j1 := eq4779 X0
       grind)
    | exact resolve eq42 eq4779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq4779
  have eq4844 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4825 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4825
    | (have j0 := eq4825 X0
       grind)
    | exact resolve eq4825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4825
  have eq4845 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4844 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4844
  have eq4847 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4845 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4845
    | exact resolve eq4845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4874 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4845 X0
       grind)
    | exact superpose eq4845 eq11
    | exact resolve eq11 eq4845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4936 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4847 X0
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq4847
    | exact resolve eq4847 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4847
  have eq5175 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4936 X0
       grind)
    | exact superpose eq4936 eq11
    | exact resolve eq11 eq4936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5284 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5175 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq5175
    | exact resolve eq5175 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5175
  have eq5344 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq5284 (τ X0)
       grind)
    | exact superpose eq5284 eq38
    | exact resolve eq38 eq5284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5397 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5344 X0
       have i₂ := eq4936 X0
       grind)
    | exact superpose eq4936 eq5344
    | exact resolve eq5344 eq4936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4936 eq5344
  have eq5921 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5952 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5921 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5921
    | exact resolve eq5921 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5921
  have eq5989 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5952 X0
       have i₂ := eq5284 X0
       grind)
    | exact superpose eq5284 eq5952
    | exact resolve eq5952 eq5284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5952
  have eq6011 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq5989
  have eq115250 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4777 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4777
    | exact resolve eq4777 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115348 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X1) X0
       have i₂ := eq4777 (σ X0) X1
       grind)
    | exact superpose eq4777 eq26
    | (have j1 := eq4777 (σ X0) X1
       grind)
    | exact resolve eq26 eq4777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4777
  have eq115442 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq115348 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq115348
    | (have j0 := eq115348 X0 X1
       grind)
    | exact resolve eq115348 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115348
  have eq115493 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq115250 X0 X1
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq115250
    | (have j0 := eq115250 X0 X1
       grind)
    | exact resolve eq115250 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115250
  have eq115526 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq115442 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq115442
    | (have j0 := eq115442 X0 X1
       grind)
    | exact resolve eq115442 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115442
  have eq115597 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq115526 X0 X1
       have i₂ := eq4874 X0
       grind)
    | exact superpose eq4874 eq115526
    | (have j0 := eq115526 X0 X1
       grind)
    | exact resolve eq115526 eq4874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115526
  have eq115644 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq115597 X0 X1
       have i₂ := eq5284 X0
       grind)
    | exact superpose eq5284 eq115597
    | (have j0 := eq115597 X0 X1
       grind)
    | exact resolve eq115597 eq5284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115597
  have eq115681 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq115644 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq115644
    | (have j0 := eq115644 X0 X1
       grind)
    | exact resolve eq115644 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115644
  have eq115892 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq115493 X1 X0
       grind)
    | exact superpose eq115493 eq11
    | (have j1 := eq115493 X1 X0
       grind)
    | exact resolve eq11 eq115493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115493
  have eq116093 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115892 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq115892
    | (have j0 := eq115892 X0 X1
       grind)
    | exact resolve eq115892 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115892
  have eq117192 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq116093 X0 (τ X1)
       grind)
    | exact superpose eq116093 eq18
    | (have j1 := eq116093 X0 (τ X1)
       grind)
    | exact resolve eq18 eq116093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq116093
  have eq123266 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq115681 (τ X0) (τ X1)
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq115681
    | (have j0 := eq115681 (τ X1) (τ X0)
       grind)
    | exact resolve eq115681 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq115681
  have eq123649 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq123266 X0 X1
       have i₂ := eq5397 X1
       grind)
    | exact superpose eq5397 eq123266
    | (have j0 := eq123266 X0 X1
       grind)
    | exact resolve eq123266 eq5397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123266
  have eq123817 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq123649 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq123649
    | (have j0 := eq123649 X0 X1
       grind)
    | exact resolve eq123649 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123649
  have eq123952 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq123817 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq123817
    | (have j0 := eq123817 X0 X1
       grind)
    | exact resolve eq123817 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123817
  have eq124062 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123952 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq123952
    | (have j0 := eq123952 X0 X1
       grind)
    | exact resolve eq123952 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123952
  have eq124143 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124062 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq124062
    | (have j0 := eq124062 X0 X1
       grind)
    | exact resolve eq124062 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124062
  have eq124572 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq124143 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124143
  have eq134770 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (τ X1)
       have i₂ := eq117192 (τ X0) X1
       grind)
    | exact superpose eq117192 eq19
    | (have j1 := eq117192 (τ X0) X1
       grind)
    | exact resolve eq19 eq117192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq117192
  have eq134861 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq134770 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq134770
    | (have j0 := eq134770 X0 X1
       grind)
    | exact resolve eq134770 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134770
  have eq134969 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq134861 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq134861
    | (have j0 := eq134861 X0 X1
       grind)
    | exact resolve eq134861 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134861
  have eq135054 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq134969 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq134969
    | (have j0 := eq134969 X0 X1
       grind)
    | exact resolve eq134969 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134969
  have eq135131 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq135054 X0 X1
       have i₂ := eq5397 X0
       grind)
    | exact superpose eq5397 eq135054
    | (have j0 := eq135054 X0 X1
       grind)
    | exact resolve eq135054 eq5397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5397 eq135054
  have eq143109 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (τ (M.op X1 X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq135131 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq135131
    | (have j0 := eq135131 X1 (σ X0)
       grind)
    | exact resolve eq135131 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135131
  have eq152002 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq143109 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq143109
    | (have j0 := eq143109 X0 (σ X1)
       grind)
    | exact resolve eq143109 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143109
  have eq152208 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq152002 X0 X1
       have i₂ := eq4845 X1
       grind)
    | exact superpose eq4845 eq152002
    | (have j0 := eq152002 X0 X1
       grind)
    | exact resolve eq152002 eq4845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4845 eq152002
  have eq152311 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq152208 X0 X1
       have i₂ := eq5284 X1
       grind)
    | exact superpose eq5284 eq152208
    | (have j0 := eq152208 X0 X1
       grind)
    | exact resolve eq152208 eq5284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152208
  have eq152396 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq152311 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq152311
    | (have j0 := eq152311 X0 X1
       grind)
    | exact resolve eq152311 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152311
  have eq153424 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq208
       have i₂ := eq152396 y x
       grind)
    | exact superpose eq152396 eq208
    | (have j1 := eq152396 y x
       grind)
    | (have r₁ := eq208
       have r₂ := eq152396 y x
       grind)
    | exact resolve eq208 eq152396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq152396
  have eq153544 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq153424
  have eq153618 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq214 x y
       grind)
    | (have r₁ := eq153544
       have r₂ := eq214 x y
       grind)
    | exact resolve eq153544 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq153544
  have eq153765 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq153618
       have i₂ := eq4874 x
       grind)
    | exact superpose eq4874 eq153618
    | exact resolve eq153618 eq4874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153618
  have eq153854 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq153765
       have i₂ := eq5284 x
       grind)
    | exact superpose eq5284 eq153765
    | exact resolve eq153765 eq5284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153765
  have eq155916 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq153854
       grind)
    | exact superpose eq153854 eq16
    | exact resolve eq16 eq153854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155936 : (τ (σ x)) ≠ (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (τ (σ x)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq124572 (σ y) (σ x)
       have i₂ := eq153854
       grind)
    | exact superpose eq153854 eq124572
    | (have j0 := eq124572 (σ y) (σ x)
       grind)
    | exact resolve eq124572 eq153854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124572 eq153854
  have eq155939 : (σ y) = (M.op (σ x) (σ x)) ∨ (τ (σ x)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq155936
  have eq155944 : (σ y) = (σ (k x x)) ∨ (τ (σ x)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq155939
       have i₂ := eq4874 x
       grind)
    | exact superpose eq4874 eq155939
    | exact resolve eq155939 eq4874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4874 eq155939
  have eq155951 : (σ y) = (σ (M.op x x)) ∨ (τ (σ x)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq155944
       have i₂ := eq5284 x
       grind)
    | exact superpose eq5284 eq155944
    | exact resolve eq155944 eq5284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5284 eq155944
  have eq155952 : (σ y) = (σ (M.op x x)) ∨ (τ (σ x)) = (τ (k (σ y) (σ x))) ∨ y = (M.op x x) := by grind
  clear eq155951
  have eq155956 : (τ (σ x)) = (k (τ (σ y)) x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq155952
       have i₂ := eq26 (σ y) x
       grind)
    | exact superpose eq26 eq155952
    | exact resolve eq155952 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq155952
  have eq155957 : (k y x) = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq155956
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq155956
    | exact resolve eq155956 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155956
  have eq155958 : x = (k y x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq155957
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq155957
    | exact resolve eq155957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155957
  have eq158858 : x ≠ x ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1219 y x
       have i₂ := eq155958
       grind)
    | exact superpose eq155958 eq1219
    | (have j0 := eq1219 y x
       grind)
    | (have r₁ := eq1219 y x
       have r₂ := eq155958
       grind)
    | exact resolve eq1219 eq155958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219 eq155958
  have eq158866 : x ≠ x ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq158858
  have eq158867 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq158866
  have eq159800 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq155916
       have i₂ := eq158867
       grind)
    | exact superpose eq158867 eq155916
    | exact resolve eq155916 eq158867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155916 eq158867
  have eq159801 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq159800
  have eq159802 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq159801
  have eq159823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6011 x
       have i₂ := eq159802
       grind)
    | exact superpose eq159802 eq6011
    | exact resolve eq6011 eq159802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159802
  have eq159905 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq159823
       have r₂ := eq16
       grind)
    | exact resolve eq159823 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159823
  have eq160775 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq159905
       grind)
    | exact superpose eq159905 eq10
    | exact resolve eq10 eq159905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159905
  have eq160978 : y = (M.op x x) := by
    first
    | (have i₁ := eq160775
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq160775
    | exact resolve eq160775 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160775
  have eq161158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6011 x
       have i₂ := eq160978
       grind)
    | exact superpose eq160978 eq6011
    | exact resolve eq6011 eq160978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6011 eq160978
  have eq161250 : False := by grind
  exact eq161250

/-- `Equation3997`: `x ◇ y = (z ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation3997 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3997 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3997.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq500 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4217 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq500 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq500
    | exact resolve eq500 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq4263 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4217 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4217
    | (have j0 := eq4217 X0 X1
       grind)
    | exact resolve eq4217 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4217
  have eq4267 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X0))) ∨ (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4263 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq4263
    | (have j0 := eq4263 (τ X1) (τ X0)
       grind)
    | exact resolve eq4263 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4263
  have eq4362 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4267 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4267
    | (have j0 := eq4267 X0 X1
       grind)
    | exact resolve eq4267 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4267
  have eq21804 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq4362 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq4362 X0 X1
       grind)
    | exact superpose eq4362 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq4362 X1 X0
       grind)
    | (have r₁ := eq13 (τ X1) (τ X0)
       have r₂ := eq4362 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq4362 X0 X1
       grind)
    | exact resolve eq13 eq4362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4362
  have eq21814 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq21804 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21804
  have eq21815 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq21814 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21814
  have eq21823 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21815 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq21815
    | (have j0 := eq21815 X0 X1
       grind)
    | exact resolve eq21815 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq21815
  have eq34146 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21823 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21823
    | exact resolve eq21823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21823
  have eq34238 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq34146 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq34146
    | (have j0 := eq34146 X0 X1
       grind)
    | exact resolve eq34146 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34146
  have eq34314 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X1) X0)
       have i₂ := eq34238 X0 X1
       grind)
    | exact superpose eq34238 eq10
    | (have j1 := eq34238 X0 X1
       grind)
    | exact resolve eq10 eq34238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34238
  have eq34432 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq34314 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq34314
    | (have j0 := eq34314 X0 X1
       grind)
    | exact resolve eq34314 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq34314
  have eq34433 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34432 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34432
  have eq34454 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34433 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34433
    | exact resolve eq34433 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34509 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq34433 X1 X0
       grind)
    | exact superpose eq34433 eq19
    | (have j1 := eq34433 X1 X0
       grind)
    | exact resolve eq19 eq34433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq34433
  have eq34903 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq34454 (σ X0) (σ X1)
       grind)
    | exact superpose eq34454 eq15
    | (have j1 := eq34454 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq34454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34454
  have eq35052 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34509 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34509
    | exact resolve eq34509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34509
  have eq35224 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35052 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq35052
    | (have j0 := eq35052 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq35052 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35052
  have eq36902 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34903 x y
       grind)
    | exact superpose eq34903 eq16
    | (have j1 := eq34903 x y
       grind)
    | exact resolve eq16 eq34903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34903
  have eq37321 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq36902
       have i₂ := eq35224 x y
       grind)
    | exact superpose eq35224 eq36902
    | (have j1 := eq35224 (σ x) (σ y)
       grind)
    | (have r₁ := eq36902
       have r₂ := eq35224 x y
       grind)
    | (have r₁ := eq36902
       have r₂ := eq35224 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq36902
       have r₂ := eq35224 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq36902 eq35224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35224 eq36902
  have eq37327 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq37321
  have eq37331 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37327
       grind)
    | exact superpose eq37327 eq16
    | exact resolve eq16 eq37327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37327
  have eq37332 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq37331
       have r₂ := eq22 x
       grind)
    | exact resolve eq37331 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37331
  have eq37333 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37332
       grind)
    | exact superpose eq37332 eq16
    | exact resolve eq16 eq37332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37334 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq37332
       grind)
    | exact superpose eq37332 eq10
    | exact resolve eq10 eq37332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37332
  have eq37510 : x = y := by
    first
    | (have i₁ := eq37334
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq37334
    | exact resolve eq37334 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37334
  have eq37511 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq37333
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq37333
    | exact resolve eq37333 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37333
  have eq37512 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq37511
       have i₂ := eq37510
       grind)
    | exact superpose eq37510 eq37511
    | exact resolve eq37511 eq37510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37510 eq37511
  have eq37513 : False := by grind
  exact eq37513

/-- `Equation4007`: `x ◇ y = (z ◇ (y ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pxy_x_pxy_Equation4007 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4007 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4007.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq41 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq29
    | exact resolve eq29 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X1 X0))) = (M.op (M.op X3 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X2 (M.op X1 X0)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 X1) (M.op (M.op X3 X2) (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op (M.op X3 X2) (M.op X1 X0))
       have i₂ := eq9 X0 X1 (M.op X3 X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1 X2 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq89 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) (M.op X1 X0) (M.op X3 X2)
       have i₂ := eq63 X3 X2 X0 X1
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) X0) ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X2) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X2 X1 (M.op X1 X2)
       have i₂ := eq14 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq64 X0 X1 X2
       have i₂ := eq14 X0 (M.op X2 (M.op X1 X0))
       grind)
    | exact superpose eq14 eq64
    | (have j1 := eq14 (M.op X1 X2) X0
       grind)
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq228 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq226 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq229 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) X0) ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq224 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq231 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq228 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq228 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq228 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq233 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq229 X0 X1 X2
       have j1 := eq12 (M.op X1 X2) X0
       grind)
    | (have r₁ := eq229 X1 X1 X2
       have r₂ := eq12 (M.op X1 X2) X1
       grind)
    | exact resolve eq229 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq249 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq233 X0 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq233 X0 X1 X2
       have i₂ := eq14 X0 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq233
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq233 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 X2 : G, (k (τ (M.op X0 X1)) X2) = (τ (M.op (M.op X0 X1) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (M.op X0 X1) X2
       have i₂ := eq233 (σ X2) X0 X1
       grind)
    | exact superpose eq233 eq23
    | exact resolve eq23 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq255 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 X1)) X2) = (σ (M.op (M.op X0 X1) (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (M.op X0 X1)
       have i₂ := eq233 (τ X2) X0 X1
       grind)
    | exact superpose eq233 eq19
    | exact resolve eq19 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq249 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq249 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq249 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq268 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq231 (τ X1) X0
       grind)
    | exact superpose eq231 eq19
    | (have j1 := eq231 (τ X1) X0
       grind)
    | exact resolve eq19 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq279 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq231 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq387 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (k (τ (M.op (σ X2) (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq252 (σ X2) (M.op X1 X0) X2
       have i₂ := eq9 X0 X1 (σ X2)
       grind)
    | exact superpose eq9 eq252
    | exact resolve eq252 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k (σ (M.op (τ X2) (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq255 (τ X2) (M.op X1 X0) X2
       have i₂ := eq9 X0 X1 (τ X2)
       grind)
    | exact superpose eq9 eq255
    | exact resolve eq255 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq261 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq471 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq470 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq491 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq471 (σ X0)
       grind)
    | exact superpose eq471 eq15
    | exact resolve eq15 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq471 (τ X0)
       grind)
    | exact superpose eq471 eq32
    | exact resolve eq32 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : ∀ X0 X1 : G, (σ (k (M.op (τ X0) (τ X0)) X1)) = (k (k X0 (σ (τ X0))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 (τ X0) X1
       have i₂ := eq471 (τ X0)
       grind)
    | exact superpose eq471 eq22
    | exact resolve eq22 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq503 : ∀ X0 X1 : G, (σ (k (M.op (τ X0) (τ X0)) X1)) = (k (k X0 X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq494 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq494
    | exact resolve eq494 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq504 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq493 X0
       have i₂ := eq471 X0
       grind)
    | exact superpose eq471 eq493
    | exact resolve eq493 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq506 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq491 X0
       have i₂ := eq471 X0
       grind)
    | exact superpose eq471 eq491
    | exact resolve eq491 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq519 : ∀ X0 X1 : G, (σ (k (M.op (τ X0) (τ X0)) X1)) = (k (M.op X0 X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq503 X0 X1
       have i₂ := eq471 X0
       grind)
    | exact superpose eq471 eq503
    | exact resolve eq503 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471 eq503
  have eq541 : ∀ X0 X1 : G, (σ (k (M.op (τ X0) (τ X0)) X1)) = (M.op (M.op X0 X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq519 X0 X1
       have i₂ := eq233 (σ X1) X0 X0
       grind)
    | exact superpose eq233 eq519
    | exact resolve eq519 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq551 : ∀ X0 X1 : G, (σ (M.op (M.op (τ X0) (τ X0)) X1)) = (M.op (M.op X0 X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq541 X0 X1
       have i₂ := eq233 X1 (τ X0) (τ X0)
       grind)
    | exact superpose eq233 eq541
    | exact resolve eq541 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq557 : ∀ X0 X1 : G, (σ (M.op (τ (M.op X0 X0)) X1)) = (M.op (M.op X0 X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq551 X0 X1
       have i₂ := eq504 X0
       grind)
    | exact superpose eq504 eq551
    | exact resolve eq551 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq576 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) X1
       have i₂ := eq504 X0
       grind)
    | exact superpose eq504 eq14
    | (have j0 := eq14 (τ X0) X1
       grind)
    | exact resolve eq14 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (M.op X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq504
  have eq578 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq577 X0
       have j1 := eq279 (τ X0) (τ (M.op X0 X0))
       grind)
    | (have r₁ := eq577 X0
       have r₂ := eq279 (τ X0) (τ (M.op X0 X0))
       grind)
    | exact resolve eq577 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq577
  have eq579 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq576 X0 X1
       have j1 := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq576 X0 (M.op (τ (M.op X0 X0)) X1)
       have r₂ := eq12 (τ (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq576 X0 X1
       have r₂ := eq12 (τ X0) X1
       grind)
    | exact resolve eq576 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq585 : ∀ X0 : G, (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq578 X0
       have i₂ := eq32 (M.op X0 X0) X0
       grind)
    | exact superpose eq32 eq578
    | exact resolve eq578 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq578
  have eq589 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq585 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq585 X0
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq585
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq585 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq624 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq589 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq589 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq589 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq689 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq506 X0
       grind)
    | exact superpose eq506 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq689 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq689 X0 (M.op (σ (M.op X0 X0)) X1)
       have r₂ := eq12 (σ (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq689 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq689 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq1163 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq624 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq624
    | exact resolve eq624 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq1197 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1163 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1163
    | (have j0 := eq1163 X0 X1
       grind)
    | exact resolve eq1163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1197 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1197
    | (have j0 := eq1197 X0 X1
       grind)
    | exact resolve eq1197 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq2433 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq579 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq579
    | (have j0 := eq579 (σ X0) X1
       grind)
    | exact resolve eq579 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2444 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (σ X2)) = (σ (M.op X0 X2)) ∨ (k (τ X1) X0) = (M.op (τ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq557 X1 X2
       have i₂ := eq579 X1 X0
       grind)
    | (have i₁ := eq557 X0 X1
       have i₂ := eq579 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq579 eq557
    | (have j1 := eq579 X1 X0
       grind)
    | exact resolve eq557 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq2452 : ∀ X0 X1 : G, (σ X0) = (M.op X1 X1) ∨ (k (τ X1) X0) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1)
       have i₂ := eq579 X1 X0
       grind)
    | (have i₁ := eq11 X0
       have i₂ := eq579 X0 (τ X0)
       grind)
    | exact superpose eq579 eq11
    | (have j1 := eq579 X1 X0
       grind)
    | exact resolve eq11 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq2512 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2433 X0 X1
       have i₂ := eq506 X0
       grind)
    | exact superpose eq506 eq2433
    | (have j0 := eq2433 X0 X1
       grind)
    | exact resolve eq2433 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq2433
  have eq2522 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2512 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2512
    | (have j0 := eq2512 X0 X1
       grind)
    | exact resolve eq2512 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512
  have eq2671 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq690 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq690 X0 (σ X0)
       grind)
    | exact superpose eq690 eq10
    | (have j1 := eq690 X1 X0
       grind)
    | exact resolve eq10 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq3261 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (M.op X0 X0) (σ y)) ∨ (k (τ X0) x) = (M.op (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq2452 x X0
       grind)
    | exact superpose eq2452 eq16
    | (have j1 := eq2452 x X0
       grind)
    | exact resolve eq16 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2452
  have eq3385 : ∀ X0 : G, (k (τ X0) x) = (M.op (τ X0) x) := by
    intro X0
    first
    | (have j0 := eq3261 X0
       have j1 := eq2444 x X0 x
       grind)
    | (have r₁ := eq3261 x
       have r₂ := eq2444 x x y
       grind)
    | exact resolve eq3261 eq2444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2444 eq3261
  have eq3426 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq3385 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3385
    | exact resolve eq3385 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3435 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq3385 X0
       grind)
    | exact superpose eq3385 eq18
    | exact resolve eq18 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3439 : ∀ X0 X1 : G, (τ (k (k X0 (σ x)) X1)) = (k (M.op (τ X0) x) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 x X1
       have i₂ := eq3385 X0
       grind)
    | exact superpose eq3385 eq41
    | exact resolve eq41 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq3440 : ∀ X0 X1 : G, (τ (M.op X1 X0)) = (M.op (τ (M.op (σ x) (M.op X0 X1))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq387 X1 X0 x
       have i₂ := eq3385 (M.op (σ x) (M.op X0 X1))
       grind)
    | exact superpose eq3385 eq387
    | exact resolve eq387 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385
  have eq3442 : ∀ X0 X1 : G, (τ (k (k X0 (σ x)) X1)) = (M.op (M.op (τ X0) x) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3439 X0 X1
       have i₂ := eq233 (τ X1) (τ X0) x
       grind)
    | exact superpose eq233 eq3439
    | exact resolve eq3439 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439
  have eq3448 : ∀ X0 : G, (k X0 (τ x)) = (τ (M.op (σ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq29 X0 x
       have i₂ := eq3426 (σ X0)
       grind)
    | exact superpose eq3426 eq29
    | exact resolve eq29 eq3426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3426
  have eq4103 : ∀ X0 X1 X2 : G, (M.op x (τ (M.op (σ x) (M.op X1 X0)))) = (M.op (M.op X2 (τ (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 x (τ (M.op (σ x) (M.op X1 X0))) X2
       have i₂ := eq3440 X1 X0
       grind)
    | exact superpose eq3440 eq9
    | exact resolve eq9 eq3440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4107 : ∀ X0 X1 X2 X3 : G, (M.op x (τ (M.op (σ x) (M.op X1 X0)))) = (M.op (M.op X2 X3) (M.op (τ (M.op X0 X1)) (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X2 X3 x (τ (M.op (σ x) (M.op X1 X0)))
       have i₂ := eq3440 X1 X0
       grind)
    | exact superpose eq3440 eq63
    | exact resolve eq63 eq3440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq4108 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (M.op X2 (τ (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 x (τ (M.op (σ x) (M.op X0 X1))) X2
       have i₂ := eq3440 X0 X1
       grind)
    | exact superpose eq3440 eq64
    | exact resolve eq64 eq3440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq4116 : ∀ X0 X1 X2 : G, (k (τ (M.op X0 X1)) X2) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq233 X0 (τ (M.op (σ x) (M.op X0 X1))) x
       have i₂ := eq3440 X0 X1
       grind)
    | exact superpose eq3440 eq233
    | exact resolve eq233 eq3440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq4124 : ∀ X0 X1 X2 : G, (σ (M.op x (τ (M.op (σ x) (M.op X1 X0))))) = (k (σ (M.op (τ X2) (τ (M.op X0 X1)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq420 x (τ (M.op (σ x) (M.op X1 X0))) X2
       have i₂ := eq3440 X1 X0
       grind)
    | exact superpose eq3440 eq420
    | exact resolve eq420 eq3440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3440
  have eq4132 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) (σ X2))) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq252 X0 X1 X2
       have i₂ := eq4116 X0 X1 X2
       grind)
    | exact superpose eq4116 eq252
    | exact resolve eq252 eq4116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq4163 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op (σ X2) (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq387 X0 X1 X2
       have i₂ := eq4116 (σ X2) (M.op X1 X0) X2
       grind)
    | exact superpose eq4116 eq387
    | exact resolve eq387 eq4116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq4260 : ∀ X0 X1 : G, (k X0 (τ x)) = (M.op X1 (M.op X1 (k X0 (τ x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4108 (σ X0) x x
       have i₂ := eq3448 X0
       grind)
    | exact superpose eq3448 eq4108
    | exact resolve eq4108 eq3448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4108
  have eq4346 : ∀ X0 X1 : G, (k (k X0 (τ x)) X1) = (M.op (k X0 (τ x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4116 (σ X0) x x
       have i₂ := eq3448 X0
       grind)
    | exact superpose eq3448 eq4116
    | exact resolve eq4116 eq3448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3448 eq4116
  have eq4453 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (M.op X2 (σ (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4260 (σ (M.op (τ (τ x)) (M.op X1 X0))) X1
       have i₂ := eq420 X0 X1 (τ x)
       grind)
    | exact superpose eq420 eq4260
    | exact resolve eq4260 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4260
  have eq4535 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 X1)) X2) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4346 (σ (M.op (τ (τ x)) (M.op X1 X0))) X1
       have i₂ := eq420 X0 X1 (τ x)
       grind)
    | exact superpose eq420 eq4346
    | exact resolve eq4346 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq4346
  have eq4583 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (τ X2))) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq255 X0 X1 X2
       have i₂ := eq4535 X0 X1 X2
       grind)
    | exact superpose eq4535 eq255
    | exact resolve eq255 eq4535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq4612 : ∀ X0 X1 X2 : G, (σ (M.op x (τ (M.op (σ x) (M.op X1 X0))))) = (M.op (σ (M.op (τ X2) (τ (M.op X0 X1)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4124 X0 X1 X2
       have i₂ := eq4535 (τ X2) (τ (M.op X0 X1)) X2
       grind)
    | exact superpose eq4535 eq4124
    | exact resolve eq4124 eq4535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4124
  have eq4786 : ∀ X0 X1 : G, (k (k X0 (σ x)) X1) = (M.op (k X0 (σ x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4535 (τ X0) x x
       have i₂ := eq3435 X0
       grind)
    | exact superpose eq3435 eq4535
    | exact resolve eq4535 eq3435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4535
  have eq4817 : ∀ X0 X1 : G, (M.op (M.op (τ X0) x) (τ X1)) = (τ (M.op (k X0 (σ x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3442 X0 X1
       have i₂ := eq4786 X0 X1
       grind)
    | exact superpose eq4786 eq3442
    | exact resolve eq3442 eq4786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3442 eq4786
  have eq5172 : ∀ X0 X1 X2 : G, (τ (M.op X1 X2)) = (M.op (τ (M.op (k X0 (σ x)) (M.op X2 X1))) (M.op (τ X0) x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4163 X1 X2 (M.op (τ X0) x)
       have i₂ := eq3435 X0
       grind)
    | exact superpose eq3435 eq4163
    | exact resolve eq4163 eq3435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3435 eq4163
  have eq5287 : ∀ X0 X1 X2 : G, (τ (M.op X1 X2)) = (M.op (M.op (M.op (τ X0) x) (τ (M.op X2 X1))) (M.op (τ X0) x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5172 X0 X1 X2
       have i₂ := eq4817 X0 (M.op X2 X1)
       grind)
    | exact superpose eq4817 eq5172
    | exact resolve eq5172 eq4817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4817 eq5172
  have eq5308 : ∀ X0 X1 X2 : G, (τ (M.op X1 X2)) = (M.op (M.op x (τ X0)) (M.op (τ (M.op X2 X1)) (M.op (τ X0) x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5287 X0 X1 X2
       have i₂ := eq89 x (τ X0) (M.op (τ X0) x) (τ (M.op X2 X1))
       grind)
    | (have i₁ := eq5287 X0 X1 X2
       have i₂ := eq89 (M.op (τ X0) x) (τ (M.op X2 X1)) x (τ X0)
       grind)
    | exact superpose eq89 eq5287
    | exact resolve eq5287 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq5287
  have eq5315 : ∀ X1 X2 : G, (τ (M.op X1 X2)) = (M.op x (τ (M.op (σ x) (M.op X1 X2)))) := by
    intro X1 X2
    first
    | (have i₁ := eq5308 x X1 X2
       have i₂ := eq4107 X2 X1 x (τ x)
       grind)
    | exact superpose eq4107 eq5308
    | exact resolve eq5308 eq4107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4107 eq5308
  have eq5317 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (τ X2) (τ (M.op X0 X1)))) X2) = (σ (τ (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4612 X0 X1 X2
       have i₂ := eq5315 X1 X0
       grind)
    | exact superpose eq5315 eq4612
    | exact resolve eq4612 eq5315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4612
  have eq5319 : ∀ X0 X1 X2 : G, (τ (M.op X1 X0)) = (M.op (M.op X2 (τ (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4103 X0 X1 X2
       have i₂ := eq5315 X1 X0
       grind)
    | exact superpose eq5315 eq4103
    | exact resolve eq4103 eq5315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4103 eq5315
  have eq5334 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (σ (M.op (τ X2) (τ (M.op X0 X1)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5317 X0 X1 X2
       have i₂ := eq11 (M.op X1 X0)
       grind)
    | exact superpose eq11 eq5317
    | exact resolve eq5317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5317
  have eq5362 : ∀ X0 X1 X2 X3 : G, (τ (M.op (M.op X2 (σ (M.op X0 X1))) X2)) = (M.op (M.op X3 (τ (σ (M.op X0 X1)))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5319 X2 (M.op X2 (σ (M.op X0 X1))) X3
       have i₂ := eq4453 X0 X1 X2
       grind)
    | exact superpose eq4453 eq5319
    | exact resolve eq5319 eq4453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4453 eq5319
  have eq5492 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 X1)) X3) = (τ (M.op (M.op X2 (σ (M.op X0 X1))) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5362 X0 X1 X2 X3
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq5362
    | exact resolve eq5362 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5362
  have eq5515 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (τ (M.op (M.op X2 (σ (M.op X0 X1))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5492 X0 X1 X2 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq5492
    | exact resolve eq5492 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5492
  have eq5594 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (M.op X2 (σ (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op (M.op X2 (σ (M.op X1 X0))) X2)
       have i₂ := eq5515 X1 X0 X2
       grind)
    | exact superpose eq5515 eq11
    | exact resolve eq11 eq5515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5515
  have eq5767 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (σ (M.op X0 X1)) X2)) X3) = (σ (M.op (τ X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5594 (τ X2) (M.op X0 X1) X3
       have i₂ := eq4583 X0 X1 X2
       grind)
    | exact superpose eq4583 eq5594
    | exact resolve eq5594 eq4583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4583
  have eq5858 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 X1))) = (σ (M.op (τ X2) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5767 X0 X1 X2 x
       have i₂ := eq9 X2 (σ (M.op X0 X1)) x
       grind)
    | exact superpose eq9 eq5767
    | exact resolve eq5767 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5767
  have eq6241 : ∀ X0 X1 X2 X3 : G, (M.op (σ X2) (M.op X0 X1)) = (M.op (σ (M.op (τ X3) (M.op (τ (M.op X0 X1)) X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5334 (M.op X0 X1) (σ X2) X3
       have i₂ := eq4132 X0 X1 X2
       grind)
    | exact superpose eq4132 eq5334
    | exact resolve eq5334 eq4132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4132 eq5334
  have eq6320 : ∀ X0 X1 X2 X3 : G, (M.op (σ X2) (M.op X0 X1)) = (M.op (M.op X3 (σ (M.op (τ (M.op X0 X1)) X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6241 X0 X1 X2 X3
       have i₂ := eq5858 (τ (M.op X0 X1)) X2 X3
       grind)
    | exact superpose eq5858 eq6241
    | exact resolve eq6241 eq5858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5858 eq6241
  have eq6359 : ∀ X0 X1 X2 : G, (M.op (σ X2) (M.op X0 X1)) = (σ (M.op X2 (τ (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6320 X0 X1 X2 x
       have i₂ := eq5594 X2 (τ (M.op X0 X1)) x
       grind)
    | exact superpose eq5594 eq6320
    | exact resolve eq6320 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6320
  have eq6945 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ (M.op X0 X1))) = (σ (M.op X2 (τ (σ (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6359 (M.op X2 (σ (M.op X1 X0))) X2 X2
       have i₂ := eq5594 X0 X1 X2
       grind)
    | exact superpose eq5594 eq6359
    | exact resolve eq6359 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5594 eq6359
  have eq7024 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ (M.op X0 X1))) = (σ (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6945 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq6945
    | exact resolve eq6945 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6945
  have eq7796 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq268
    | exact resolve eq268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq7908 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7796 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7796
    | (have j0 := eq7796 X0 X1
       grind)
    | exact resolve eq7796 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7796
  have eq8682 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2671 (σ X1) X0
       grind)
    | exact superpose eq2671 eq15
    | (have j1 := eq2671 (σ X1) X0
       grind)
    | exact resolve eq15 eq2671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671
  have eq8707 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8682 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8682
    | (have j0 := eq8682 X0 X1
       grind)
    | exact resolve eq8682 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8682
  have eq9229 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7908 X1 X0
       have i₂ := eq1199 X0 X1
       grind)
    | exact superpose eq1199 eq7908
    | (have j0 := eq7908 X1 X0
       have j1 := eq1199 X0 X1
       grind)
    | exact resolve eq7908 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199 eq7908
  have eq9248 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq9229 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9229
  have eq12286 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9248 x y
       grind)
    | exact superpose eq9248 eq16
    | (have j1 := eq9248 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq9248 x y
       grind)
    | exact resolve eq16 eq9248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9248
  have eq12348 : x = (k x y) := by grind
  clear eq12286
  have eq12418 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2522 x y
       have i₂ := eq12348
       grind)
    | exact superpose eq12348 eq2522
    | (have j0 := eq2522 x y
       grind)
    | exact resolve eq2522 eq12348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522
  have eq12420 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8707 x y
       have i₂ := eq12348
       grind)
    | exact superpose eq12348 eq8707
    | (have j0 := eq8707 x y
       grind)
    | exact resolve eq8707 eq12348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8707 eq12348
  have eq13344 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12420
       grind)
    | exact superpose eq12420 eq16
    | exact resolve eq16 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12420
  have eq13411 : (σ x) ≠ (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13344
       have i₂ := eq12418
       grind)
    | exact superpose eq12418 eq13344
    | exact resolve eq13344 eq12418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12418 eq13344
  have eq13415 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by grind
  clear eq13411
  have eq13416 : y = (M.op x x) := by grind
  clear eq13415
  have eq13495 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq7024 x x x
       have i₂ := eq13416
       grind)
    | exact superpose eq13416 eq7024
    | exact resolve eq7024 eq13416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7024 eq13416
  have eq13497 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13495 x
       grind)
    | exact superpose eq13495 eq16
    | (have r₁ := eq16
       have r₂ := eq13495 x
       grind)
    | exact resolve eq16 eq13495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13495
  have eq13498 : False := by grind
  exact eq13498

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_x_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) x X2
       have i₂ := eq9 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq21 X0 X2
       grind)
    | (have i₁ := eq21 X0 X2
       have i₂ := eq21 X0 (M.op X0 X0)
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq90 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq202 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq88 x y
       grind)
    | exact superpose eq88 eq16
    | (have j1 := eq88 x x
       grind)
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq507 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | (have j0 := eq90 X1 X1
       grind)
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq545 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq507 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq507
    | (have j0 := eq507 X1 X1
       grind)
    | exact resolve eq507 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq1426 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq202
       have i₂ := eq545 y x
       grind)
    | exact superpose eq545 eq202
    | (have j1 := eq545 (σ x) (σ x)
       grind)
    | (have r₁ := eq202
       have r₂ := eq545 y x
       grind)
    | exact resolve eq202 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq545
  have eq1427 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1426
  have eq3004 : ∀ X0 X1 : G, (σ X1) ≠ X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq4035 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3004 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3004
    | (have r₁ := eq3004 X0 (τ X0)
       have r₂ := eq11 X0
       grind)
    | (have r₁ := eq3004 (σ (τ (σ X1))) X1
       have r₂ := eq11 (σ X1)
       grind)
    | exact resolve eq3004 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3004
  have eq4057 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4035 X0 X1
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq4035
    | (have j0 := eq4035 X0 X1
       grind)
    | (have r₁ := eq4035 (k (τ X1) (τ X0)) (τ (k X1 X0))
       have r₂ := eq37 X0 X1
       grind)
    | (have r₁ := eq4035 (τ (k X1 X0)) (k (τ X1) (τ X0))
       have r₂ := eq37 X0 X1
       grind)
    | exact resolve eq4035 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4035
  have eq4106 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq4057 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4057
  have eq4140 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq4106 (σ X0)
       grind)
    | exact superpose eq4106 eq41
    | (have j1 := eq4106 (σ X0)
       grind)
    | exact resolve eq41 eq4106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4106
  have eq4159 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4140 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4140
    | (have j0 := eq4140 X0
       grind)
    | exact resolve eq4140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4140
  have eq4169 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4159 X0
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq4159
    | (have j0 := eq4159 X0
       grind)
    | exact resolve eq4159 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4159
  have eq4174 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4169 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4169
    | (have j0 := eq4169 X0
       grind)
    | exact resolve eq4169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4169
  have eq4175 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4174 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4174
  have eq4243 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4175 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4175
    | exact resolve eq4175 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4269 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4175 X0
       grind)
    | exact superpose eq4175 eq11
    | exact resolve eq11 eq4175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4175
  have eq4334 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4243 X0
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq4243
    | exact resolve eq4243 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4243
  have eq4358 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4334 X0
       grind)
    | exact superpose eq4334 eq11
    | exact resolve eq11 eq4334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334
  have eq4469 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4358 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4358
    | exact resolve eq4358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4358
  have eq4936 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq4937 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) x
       have i₂ := eq4269 X0
       grind)
    | exact superpose eq4269 eq21
    | exact resolve eq21 eq4269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq4959 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = (σ (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4937 X0 X1
       have i₂ := eq4269 (k X0 X0)
       grind)
    | exact superpose eq4269 eq4937
    | exact resolve eq4937 eq4269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4937
  have eq4960 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4936 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq4936
    | exact resolve eq4936 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4936
  have eq5003 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = (σ (M.op (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4959 X0 X1
       have i₂ := eq4469 (k X0 X0)
       grind)
    | exact superpose eq4469 eq4959
    | exact resolve eq4959 eq4469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4959
  have eq5004 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4960 X0
       have i₂ := eq4469 X0
       grind)
    | exact superpose eq4469 eq4960
    | exact resolve eq4960 eq4469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4960
  have eq5031 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5003 X0 X1
       have i₂ := eq4469 X0
       grind)
    | exact superpose eq4469 eq5003
    | exact resolve eq5003 eq4469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5003
  have eq5032 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq5004
  have eq10810 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5031 X0 X2
       have i₂ := eq73 X0 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq5031 X0 X2
       have i₂ := eq73 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq73 eq5031
    | exact resolve eq5031 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq12060 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X1)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5031 X0 x
       have i₂ := eq10810 X0 X1 x
       grind)
    | exact superpose eq10810 eq5031
    | exact resolve eq5031 eq10810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5031
  have eq625372 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5032 x
       have i₂ := eq1427
       grind)
    | exact superpose eq1427 eq5032
    | exact resolve eq5032 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq625965 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq625372
       have r₂ := eq16
       grind)
    | exact resolve eq625372 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625372
  have eq626290 : (σ y) = (σ (k x x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq625965
       have i₂ := eq4269 x
       grind)
    | exact superpose eq4269 eq625965
    | exact resolve eq625965 eq4269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625965
  have eq626615 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq626290
       have i₂ := eq4469 x
       grind)
    | exact superpose eq4469 eq626290
    | exact resolve eq626290 eq4469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626290
  have eq626940 : (σ x) = (σ (k x x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq626615
       have i₂ := eq4269 x
       grind)
    | exact superpose eq4269 eq626615
    | exact resolve eq626615 eq4269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4269 eq626615
  have eq626970 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq626940
       have i₂ := eq4469 x
       grind)
    | exact superpose eq4469 eq626940
    | exact resolve eq626940 eq4469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4469 eq626940
  have eq627117 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq626970
       grind)
    | exact superpose eq626970 eq10
    | exact resolve eq10 eq626970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626970
  have eq627423 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq627117
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq627117
    | exact resolve eq627117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627117
  have eq628979 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq627423
       grind)
    | exact superpose eq627423 eq10
    | exact resolve eq10 eq627423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627423
  have eq629290 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq628979
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq628979
    | exact resolve eq628979 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628979
  have eq629291 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq629290
  have eq629405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5032 x
       have i₂ := eq629291
       grind)
    | exact superpose eq629291 eq5032
    | exact resolve eq5032 eq629291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5032 eq629291
  have eq629701 : x = (M.op x x) := by
    first
    | (have r₁ := eq629405
       have r₂ := eq16
       grind)
    | exact resolve eq629405 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629405
  have eq631589 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X1 x
       have i₂ := eq629701
       grind)
    | exact superpose eq629701 eq9
    | exact resolve eq9 eq629701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631662 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq12060 x x
       have i₂ := eq629701
       grind)
    | exact superpose eq629701 eq12060
    | exact resolve eq12060 eq629701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12060
  have eq631930 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq631662 X0
       have i₂ := eq629701
       grind)
    | exact superpose eq629701 eq631662
    | exact resolve eq631662 eq629701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629701 eq631662
  have eq641625 : ∀ X0 X1 : G, (σ (M.op (M.op x x) X0)) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10810 x X0 X1
       have i₂ := eq631930 x
       grind)
    | exact superpose eq631930 eq10810
    | exact resolve eq10810 eq631930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10810
  have eq642124 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq641625 x X1
       have i₂ := eq631589 x x
       grind)
    | exact superpose eq631589 eq641625
    | exact resolve eq641625 eq631589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631589 eq641625
  have eq650045 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq642124 (σ y)
       grind)
    | exact superpose eq642124 eq16
    | exact resolve eq16 eq642124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642124
  have eq650649 : False := by grind
  exact eq650649

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyy_x_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
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
  clear eq43
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X1) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) X1 X2
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq53 X0 x X2 X3
       have i₂ := eq14 X0 x (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq71 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq81 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq85 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq121 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120
    | exact resolve eq120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq219 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (k X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq58 X0 X1 X2
       grind)
    | exact superpose eq58 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = (k X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq452 X0 X1 X2
       have i₂ := eq58 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq58 eq452
    | (have j0 := eq452 X0 X1 X2
       grind)
    | exact resolve eq452 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq685 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op X0 X1) X1 X2
       have i₂ := eq14 X0 X1 (M.op (M.op X0 X1) X1)
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq987 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq986
    | exact resolve eq986 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq990 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq987
       have r₂ := eq27
       grind)
    | exact resolve eq987 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq992 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq990
    | exact resolve eq990 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq994 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq992
    | exact resolve eq992 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1169 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq994 eq85
    | (have r₁ := eq85
       have r₂ := eq994
       grind)
    | exact resolve eq85 eq994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1173 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq994 eq27
    | exact resolve eq27 eq994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1174 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq994
  have eq1175 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1169
  have eq1177 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1175
       have r₂ := eq1174
       grind)
    | exact resolve eq1175 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174 eq1175
  have eq1313 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1177 eq122
    | exact resolve eq122 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1314 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1177 eq90
    | exact resolve eq90 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1177
  have eq1317 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1313
  have eq1321 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1314
    | exact resolve eq1314 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1314
  have eq1322 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1317
       have r₂ := eq1173
       grind)
    | exact resolve eq1317 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173 eq1317
  have eq1325 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1321
       have r₂ := eq84
       grind)
    | exact resolve eq1321 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq1321
  have eq1328 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1322 eq55
    | exact resolve eq55 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1329 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1322 eq71
    | (have r₁ := eq71
       have r₂ := eq1322
       grind)
    | exact resolve eq71 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1331 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1329
  have eq1334 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1328
    | (have j0 := eq1328 X0
       grind)
    | exact resolve eq1328 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq1430 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq1325
       grind)
    | exact superpose eq1325 eq79
    | exact resolve eq79 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq1325
  have eq1435 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1430
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1430
    | exact resolve eq1430 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1441 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1435 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435
  have eq1442 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1441
  have eq1446 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1442
    | exact resolve eq1442 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442
  have eq1449 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1446
    | exact resolve eq1446 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq1450 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1449
  have eq1554 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1450 eq27
    | exact resolve eq27 eq1450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450
  have eq1616 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1331 eq122
    | exact resolve eq122 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq1331
  have eq1619 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1616
  have eq1767 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1322 eq1334
    | exact resolve eq1334 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322 eq1334
  have eq1786 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1767 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767
  have eq1807 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1786
    | (have j0 := eq1786 (σ y)
       grind)
    | exact resolve eq1786 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq1852 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1807 eq1619
    | exact resolve eq1619 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619 eq1807
  have eq1868 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1852
  have eq1876 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1868
       have r₂ := eq27
       grind)
    | exact resolve eq1868 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868
  have eq1878 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1876 eq20
    | exact resolve eq20 eq1876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq1902 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1878
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1878
    | exact resolve eq1878 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1878
  have eq1920 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1902 eq1554
    | (have r₁ := eq1554
       have r₂ := eq1902
       grind)
    | exact resolve eq1554 eq1902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554 eq1902
  have eq1923 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1920
  have eq1924 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1923
  have eq1944 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1924 eq55
    | exact resolve eq55 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1953 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1944
    | (have j0 := eq1944 X0
       grind)
    | exact resolve eq1944 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq2546 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1924 eq1953
    | exact resolve eq1953 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2572 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2546 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2546
  have eq2954 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2572
    | (have j0 := eq2572 (σ y)
       grind)
    | exact resolve eq2572 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2572
  have eq3017 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2954 eq58
    | exact resolve eq58 eq2954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq2954
  have eq3473 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) X1) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq1953 eq3017
    | exact resolve eq3017 eq1953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953 eq3017
  have eq3520 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) X1) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq3473 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3473
  have eq3531 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq225 eq3520
    | exact resolve eq3520 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq3520
  have eq3554 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3531 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq3531
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3531
       grind)
    | exact resolve eq13 eq3531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3531
  have eq3565 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq3554
  have eq3688 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1924 eq3565
    | exact resolve eq3565 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924 eq3565
  have eq3699 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3688
  have eq3922 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3699 eq49
    | exact resolve eq49 eq3699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3699
  have eq3928 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq3922
    | exact resolve eq3922 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3922
  have eq4949 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq3928
       grind)
    | exact superpose eq3928 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq3928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3928
  have eq4950 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq4949
  have eq5247 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq219 X0
       have i₂ := eq4950
       grind)
    | exact superpose eq4950 eq219
    | exact resolve eq219 eq4950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5265 : ∀ X0 : G, x = (M.op (M.op x x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq685 x x x
       have i₂ := eq4950
       grind)
    | exact superpose eq4950 eq685
    | exact resolve eq685 eq4950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq4950
  have eq5271 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5265 x
       have i₂ := eq219 x
       grind)
    | exact superpose eq219 eq5265
    | exact resolve eq5265 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq5265
  have eq15157 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5247 eq5271
    | exact resolve eq5271 eq5247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5247 eq5271
  have eq15217 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15157 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15157
  have eq15277 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15217 y
       grind)
    | exact superpose eq15217 eq18
    | (have j1 := eq15217 y
       grind)
    | exact resolve eq18 eq15217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15217
  have eq15314 : x = (M.op x y) := by grind
  clear eq15277
  have eq15336 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15314 eq20
    | exact resolve eq20 eq15314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15338 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq15314 eq54
    | exact resolve eq54 eq15314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq15371 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq15338 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15338
    | (have j0 := eq15338 X0
       grind)
    | exact resolve eq15338 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15338
  have eq15373 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15336
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15336
    | exact resolve eq15336 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15336
  have eq15375 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq15314 eq15371
    | exact resolve eq15371 eq15314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15371
  have eq15378 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15373 eq26
    | exact resolve eq26 eq15373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq15586 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15375 y
       grind)
    | exact superpose eq15375 eq18
    | (have j1 := eq15375 y
       grind)
    | exact resolve eq18 eq15375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq15627 : x = (M.op x x) := by
    first
    | exact superpose eq15314 eq15586
    | exact resolve eq15586 eq15314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15314 eq15586
  have eq15651 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq15627
       have i₂ := eq15375 X0
       grind)
    | (have i₁ := eq15627
       have i₂ := eq15375 x
       grind)
    | exact superpose eq15375 eq15627
    | exact resolve eq15627 eq15375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15627
  have eq15906 : ∀ X0 X1 X2 : G, (M.op x X0) ≠ (M.op (M.op x X0) X1) ∨ (M.op x X0) = (k X2 (M.op (M.op x X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq455 x X1 X2
       have i₂ := eq15375 X0
       grind)
    | (have i₁ := eq455 x X1 X2
       have i₂ := eq15375 x
       grind)
    | exact superpose eq15375 eq455
    | exact resolve eq455 eq15375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq15375
  have eq15982 : ∀ X0 X1 X2 : G, x ≠ (M.op x X1) ∨ (M.op x X0) = (k X2 (M.op (M.op x X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15906 X0 X1 X2
       have i₂ := eq15651 X0
       grind)
    | exact superpose eq15651 eq15906
    | (have j0 := eq15906 X0 X1 X2
       grind)
    | exact resolve eq15906 eq15651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15906
  have eq16007 : ∀ X0 X1 X2 : G, (M.op x X0) = (k X2 (M.op (M.op x X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq15982 X0 X1 X2
       grind)
    | (have r₁ := eq15982 X0 X0 X2
       have r₂ := eq15651 X0
       grind)
    | exact resolve eq15982 eq15651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15982
  have eq16023 : ∀ X1 X2 : G, x = (k X2 (M.op x X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq16007 x X1 X2
       have i₂ := eq15651 x
       grind)
    | exact superpose eq15651 eq16007
    | exact resolve eq16007 eq15651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16007
  have eq16027 : ∀ X2 : G, x = (k X2 x) := by
    intro X2
    first
    | (have i₁ := eq16023 x X2
       have i₂ := eq15651 x
       grind)
    | exact superpose eq15651 eq16023
    | exact resolve eq16023 eq15651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15651 eq16023
  have eq16057 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x
       have i₂ := eq16027 (τ X0)
       grind)
    | exact superpose eq16027 eq34
    | exact resolve eq34 eq16027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq16027
  have eq16076 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16057 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16057
    | (have j0 := eq16057 X0
       grind)
    | exact resolve eq16057 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16057
  have eq16090 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq15373 eq16076
    | exact resolve eq16076 eq15373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16076
  have eq17541 : (σ (k y (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq103
    | (have j0 := eq103 (M.op x y)
       grind)
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq103
  have eq17577 : (M.op (σ x) (σ y)) = (σ (k y (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15378 eq17541
    | exact resolve eq17541 eq15378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17541
  have eq17604 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq81 eq17577
    | exact resolve eq17577 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq17577
  have eq17622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16090 eq17604
    | exact resolve eq17604 eq16090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17604
  have eq17637 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq17622
       have r₂ := eq27
       grind)
    | exact resolve eq17622 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17622
  have eq17649 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15378 eq17637
    | exact resolve eq17637 eq15378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17637
  have eq17661 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15378 eq17649
    | exact resolve eq17649 eq15378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15378 eq17649
  have eq17673 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17661
       have r₂ := eq27
       grind)
    | exact resolve eq17661 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17661
  have eq17758 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq17673 eq27
    | exact resolve eq27 eq17673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq17761 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq17673 eq85
    | (have r₁ := eq85
       have r₂ := eq17673
       grind)
    | exact resolve eq85 eq17673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq17673
  have eq17832 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq17761
  have eq17837 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq15373 eq17832
    | exact resolve eq17832 eq15373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17832
  have eq17844 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15373 eq17837
    | exact resolve eq17837 eq15373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15373 eq17837
  have eq17850 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16090 eq17844
    | exact resolve eq17844 eq16090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16090 eq17844
  have eq17851 : (σ (M.op x y)) = (σ y) := by grind
  clear eq17850
  have eq17863 : False := by grind
  exact eq17863

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then Y else if m(Y,Y) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_y_y_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
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
  have eq50 : x ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X1) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) X1 X2
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq59 X0 x X2 X3
       have i₂ := eq14 X0 x (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq73 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq120
    | exact resolve eq120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq220 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq38
  have eq404 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) X4) (M.op (M.op X0 X2) X4)) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X0 X2) X4 X3
       have i₂ := eq62 X0 X2 X1
       grind)
    | (have i₁ := eq62 (M.op X0 X0) X1 X2
       have i₂ := eq62 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) X1) (M.op (σ x) X1)) := by
    intro X1
    first
    | exact superpose eq220 eq62
    | exact resolve eq62 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X2 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X2) X4) (M.op (M.op X0 X2) X4)) := by
    intro X0 X2 X4
    first
    | (have i₁ := eq404 X0 x X2 x X4
       have i₂ := eq66 X0 x x
       grind)
    | exact superpose eq66 eq404
    | exact resolve eq404 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq404
  have eq1560 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq100 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1562 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1560 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560
  have eq6713 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1562 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq1562
    | (have j0 := eq1562 (τ X0)
       grind)
    | exact resolve eq1562 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1562
  have eq6721 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6713 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6713
    | (have j0 := eq6713 X0
       grind)
    | exact resolve eq6713 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6713
  have eq6727 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6721 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6721
    | (have j0 := eq6721 X0
       grind)
    | exact resolve eq6721 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6721
  have eq9466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq123 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq9467 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq9466
    | exact resolve eq9466 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9466
  have eq9478 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq9467
       have r₂ := eq27
       grind)
    | exact resolve eq9467 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9467
  have eq9480 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq9478
    | exact resolve eq9478 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9478
  have eq9506 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq9480 eq73
    | (have j0 := eq73 X0 (σ x)
       grind)
    | (have r₁ := eq73 X0 (σ x)
       have r₂ := eq9480
       grind)
    | (have r₁ := eq73 X0 x
       have r₂ := eq9480
       grind)
    | exact resolve eq73 eq9480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9480
  have eq9510 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq9506 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9506
  have eq9571 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq9510 eq86
    | exact resolve eq86 eq9510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq9510
  have eq9613 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq9571
    | exact resolve eq9571 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9571
  have eq9644 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq9613
       have r₂ := eq50
       grind)
    | exact resolve eq9613 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq9613
  have eq9656 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq73 y x
       grind)
    | (have r₁ := eq9644
       have r₂ := eq73 x x
       grind)
    | exact resolve eq9644 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9644
  have eq9658 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq9656
       grind)
    | exact superpose eq9656 eq79
    | exact resolve eq79 eq9656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq9656
  have eq9675 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9658
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9658
    | exact resolve eq9658 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9658
  have eq9677 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq9675
       have r₂ := eq51
       grind)
    | exact resolve eq9675 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq9675
  have eq9690 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9677 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq9677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9677
  have eq9691 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq9690
  have eq9693 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9691
    | exact resolve eq9691 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9691
  have eq9724 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9693 eq220
    | exact resolve eq220 eq9693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq9742 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9693 eq479
    | exact resolve eq479 eq9693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq9693
  have eq9758 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq413 eq9742
    | (have j0 := eq9742 (σ y)
       grind)
    | exact resolve eq9742 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq9742
  have eq12482 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9724 eq9758
    | exact resolve eq9758 eq9724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9724 eq9758
  have eq12543 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq12482 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12482
  have eq12603 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12543 eq26
    | (have j1 := eq12543 (σ y)
       grind)
    | exact resolve eq26 eq12543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12543
  have eq12641 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12603
  have eq12662 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq12641 eq27
    | exact resolve eq27 eq12641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq12664 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq12641 eq61
    | exact resolve eq61 eq12641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq12677 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq12664
    | (have j0 := eq12664 X0
       grind)
    | exact resolve eq12664 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12664
  have eq12679 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq12641 eq12677
    | exact resolve eq12677 eq12641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12677
  have eq12727 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12679 eq26
    | (have j1 := eq12679 (σ y)
       grind)
    | exact resolve eq26 eq12679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq12679
  have eq12769 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12641 eq12727
    | exact resolve eq12727 eq12641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12641 eq12727
  have eq12820 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq12769 eq73
    | (have j0 := eq73 X0 (σ x)
       grind)
    | (have r₁ := eq73 X0 (σ x)
       have r₂ := eq12769
       grind)
    | exact resolve eq73 eq12769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq12769
  have eq12824 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq12820 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12820
  have eq13036 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) := by
    intro X0
    first
    | exact superpose eq12824 eq341
    | exact resolve eq341 eq12824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq12824
  have eq13045 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | exact superpose eq28 eq13036
    | exact resolve eq13036 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13036
  have eq13134 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6727 x
       have i₂ := eq13045 x
       grind)
    | exact superpose eq13045 eq6727
    | (have j0 := eq6727 x
       grind)
    | (have r₁ := eq6727 x
       have r₂ := eq13045 x
       grind)
    | exact resolve eq6727 eq13045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6727 eq13045
  have eq13153 : x = (M.op x x) := by grind
  clear eq13134
  have eq13224 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq62 x x x
       have i₂ := eq13153
       grind)
    | exact superpose eq13153 eq62
    | exact resolve eq62 eq13153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq13263 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13224 X0
       have i₂ := eq13153
       grind)
    | exact superpose eq13153 eq13224
    | exact resolve eq13224 eq13153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13153 eq13224
  have eq14223 : x = (M.op x y) := by
    first
    | (have i₁ := eq13263 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13263
    | (have j0 := eq13263 y
       grind)
    | exact resolve eq13263 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq13263
  have eq14336 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq14223 eq20
    | exact resolve eq20 eq14223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq14223
  have eq14455 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14336
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14336
    | exact resolve eq14336 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq14336
  have eq14499 : False := by grind
  exact eq14499

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyy_pxx_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
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
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) X1) X2 X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq177 X0 x X2 X3
       have i₂ := eq16 X0 x (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) X2) ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X1) X2) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X0) = (k X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X0 X1) X1)
       have i₂ := eq16 X0 X1 (M.op (M.op X0 X1) X1)
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq991 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X1) X2) = X0 ∨ (M.op (M.op (M.op X0 X1) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq11
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1001 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (M.op (M.op X0 X2) X2)) ∨ (M.op X0 X0) = (M.op (M.op X0 X2) X2) ∨ (M.op (M.op X0 X2) X2) = (M.op (M.op (M.op X0 X2) X2) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X2 (M.op (M.op X0 X1) X1)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq11
    | (have j0 := eq11 (M.op (M.op X0 X2) X2) (M.op (M.op X0 X2) X2)
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1009 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq1010 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1074 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq991 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1097 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (M.op (M.op X0 X2) X2)) ∨ (M.op (M.op X0 X2) X2) = (M.op (M.op (M.op X0 X2) X2) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1001 X0 X1 X2
       have j1 := eq184 X0 X2 X1
       grind)
    | (have r₁ := eq1001 X0 X1 X1
       have r₂ := eq184 X0 X1 X2
       grind)
    | exact resolve eq1001 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1107 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1074 X0 X1 X2
       have j1 := eq183 X0 X1 X2 X0
       grind)
    | (have r₁ := eq1074 X0 X1 X2
       have r₂ := eq183 X0 X1 X2 x
       grind)
    | exact resolve eq1074 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq1074
  have eq1123 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X2) X2) ∨ (M.op X0 X0) = (k X1 (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1097 X0 X1 X2
       have i₂ := eq16 X0 X2 (M.op (M.op X0 X2) X2)
       grind)
    | exact superpose eq16 eq1097
    | (have j0 := eq1097 X0 X1 X2
       grind)
    | exact resolve eq1097 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1140 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1123 X0 X1 X2
       have j1 := eq184 X0 X2 X1
       grind)
    | (have r₁ := eq1123 X0 X1 X1
       have r₂ := eq184 X0 X1 X2
       grind)
    | exact resolve eq1123 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq1123
  have eq1279 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq1107
    | (have j0 := eq1107 (σ x) (σ y) X0
       grind)
    | exact resolve eq1107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1304 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq182 X0 X0 x
       have i₂ := eq1107 X0 X0 x
       grind)
    | exact superpose eq1107 eq182
    | exact resolve eq182 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1309 : ∀ X0 X2 X3 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq182 (M.op (M.op X0 x) x) X2 X3
       have i₂ := eq1107 X0 x (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq1107 eq182
    | exact resolve eq182 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1401 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1304 X0
       grind)
    | exact superpose eq1304 eq13
    | exact resolve eq13 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2130 : ∀ X0 X1 X2 X3 : G, (k X1 X1) = (M.op (k X0 (M.op (M.op (k X1 X1) X2) X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1309 X1 (k X1 X1) X3
       have i₂ := eq1140 (k X1 X1) X0 X2
       grind)
    | exact superpose eq1140 eq1309
    | exact resolve eq1309 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq2178 : ∀ X0 X1 X3 : G, (k X1 X1) = (M.op (k X0 (k X1 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2130 X0 X1 x X3
       have i₂ := eq1309 X1 x x
       grind)
    | exact superpose eq1309 eq2130
    | exact resolve eq2130 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309 eq2130
  have eq2354 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1009
       grind)
    | exact superpose eq1009 eq39
    | exact resolve eq39 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq2355 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2354
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2354
    | exact resolve eq2354 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2354
  have eq2357 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq2355
    | exact resolve eq2355 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2355
  have eq2359 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2357
       have i₂ := eq1304 x
       grind)
    | exact superpose eq1304 eq2357
    | exact resolve eq2357 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2357
  have eq11955 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2359 eq1010
    | exact resolve eq1010 eq2359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010 eq2359
  have eq11964 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11955
       have r₂ := eq27
       grind)
    | exact resolve eq11955 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11955
  have eq11969 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11964
       have i₂ := eq1304 sF2
       grind)
    | exact superpose eq1304 eq11964
    | exact resolve eq11964 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304 eq11964
  have eq11983 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11969 eq141
    | exact resolve eq141 eq11969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11969
  have eq12006 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq11983
    | exact resolve eq11983 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11983
  have eq12007 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12006
  have eq12029 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq12007
       grind)
    | exact superpose eq12007 eq39
    | exact resolve eq39 eq12007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq12034 : ∀ X0 : G, x ≠ x ∨ x = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1401 x x
       have i₂ := eq12007
       grind)
    | exact superpose eq12007 eq1401
    | (have r₁ := eq1401 x x
       have r₂ := eq12007
       grind)
    | exact resolve eq1401 eq12007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12007
  have eq12046 : ∀ X0 : G, x = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12034 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12034
  have eq12052 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12029
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12029
    | exact resolve eq12029 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12029
  have eq12075 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x
       have i₂ := eq12046 (τ X0)
       grind)
    | exact superpose eq12046 eq34
    | exact resolve eq34 eq12046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12046
  have eq12100 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12075 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12075
    | (have j0 := eq12075 X0
       grind)
    | exact resolve eq12075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12075
  have eq12134 : ∀ X0 X1 : G, (σ x) = (M.op (k X0 (σ x)) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq12052 eq2178
    | exact resolve eq2178 eq12052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12052
  have eq12143 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq12100 eq12134
    | exact resolve eq12134 eq12100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12100 eq12134
  have eq13793 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12143 eq26
    | (have j1 := eq12143 (σ y)
       grind)
    | exact resolve eq26 eq12143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12143
  have eq13837 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13793
  have eq13897 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13837 eq1279
    | exact resolve eq1279 eq13837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279
  have eq13920 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq13897
    | (have j0 := eq13897 X0
       grind)
    | exact resolve eq13897 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13897
  have eq13953 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13837 eq13920
    | exact resolve eq13920 eq13837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13920
  have eq14272 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13953 eq26
    | (have j1 := eq13953 (σ y)
       grind)
    | exact resolve eq26 eq13953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13953
  have eq14339 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13837 eq14272
    | exact resolve eq14272 eq13837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13837 eq14272
  have eq14385 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14339 eq141
    | exact resolve eq141 eq14339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq14390 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14339 eq1401
    | (have r₁ := eq1401 (σ x) x
       have r₂ := eq14339
       grind)
    | exact resolve eq1401 eq14339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14339
  have eq14404 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14390 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14390
  have eq14417 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq14385
    | exact resolve eq14385 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14385
  have eq14470 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14404 eq389
    | exact resolve eq389 eq14404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq14404
  have eq14521 : ∀ X0 : G, x = (k X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq14470
    | exact resolve eq14470 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14470
  have eq14572 : ∀ X0 X1 : G, x = (M.op (k X0 x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq2178 X0 x x
       have i₂ := eq14417
       grind)
    | exact superpose eq14417 eq2178
    | exact resolve eq2178 eq14417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14417
  have eq14586 : ∀ X1 : G, x = (M.op x X1) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq14521 eq14572
    | exact resolve eq14572 eq14521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14521 eq14572
  have eq14786 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14586 y
       grind)
    | exact superpose eq14586 eq18
    | (have j1 := eq14586 y
       grind)
    | exact resolve eq18 eq14586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14586
  have eq14830 : x = (M.op x y) := by grind
  clear eq14786
  have eq14866 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14830
       grind)
    | exact superpose eq14830 eq18
    | exact resolve eq18 eq14830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq14867 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq14830
       grind)
    | exact superpose eq14830 eq22
    | exact resolve eq22 eq14830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq14830
  have eq14956 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14867 eq20
    | exact resolve eq20 eq14867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14867
  have eq15095 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq14866 eq1107
    | exact resolve eq1107 eq14866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq15113 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq14866 eq15095
    | exact resolve eq15095 eq14866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15095
  have eq15360 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq15113 eq14866
    | exact resolve eq14866 eq15113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14866 eq15113
  have eq16487 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15360 eq37
    | exact resolve eq37 eq15360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq16493 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq15360 eq1401
    | (have r₁ := eq1401 (M.op x y) x
       have r₂ := eq15360
       grind)
    | exact resolve eq1401 eq15360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401 eq15360
  have eq16507 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq16493 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16493
  have eq16523 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16487
    | exact resolve eq16487 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16487
  have eq16535 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq14956 eq16523
    | exact resolve eq16523 eq14956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16523
  have eq16571 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq16507 eq34
    | exact resolve eq34 eq16507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq16507
  have eq16606 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq16571
    | (have j0 := eq16571 X0
       grind)
    | exact resolve eq16571 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq16571
  have eq16624 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq14956 eq16606
    | exact resolve eq16606 eq14956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16606
  have eq16666 : ∀ X0 X1 : G, (σ x) = (M.op (k X0 (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq16535 eq2178
    | exact resolve eq2178 eq16535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178 eq16535
  have eq16678 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) := by
    intro X1
    first
    | exact superpose eq16624 eq16666
    | exact resolve eq16666 eq16624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16624 eq16666
  have eq16833 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16678 eq26
    | (have j1 := eq16678 (σ y)
       grind)
    | exact resolve eq26 eq16678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq16678
  have eq16956 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq16833 eq27
    | exact resolve eq27 eq16833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16833
  have eq17024 : False := by grind
  exact eq17024
