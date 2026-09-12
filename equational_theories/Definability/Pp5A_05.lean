import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1682`: `x = (y ◇ x) ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation1682 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1682 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1682.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq162 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq163 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
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
  have eq3375 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq162 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq4441 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = X1 ∨ (σ X0) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq163 X1 X0
       grind)
    | exact superpose eq163 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq163 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq163 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq163 (M.op X1 (σ X1)) X1
       grind)
    | exact resolve eq13 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq4471 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = X1 ∨ (σ X0) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4441 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4441
  have eq4472 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4471 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4471
  have eq5304 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4472 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4472
    | exact resolve eq4472 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5335 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq4472 X0 X1
       grind)
    | exact superpose eq4472 eq37
    | (have j1 := eq4472 X0 X1
       grind)
    | exact resolve eq37 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4472
  have eq5416 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5335 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5335
    | (have j0 := eq5335 X0 X1
       grind)
    | exact resolve eq5335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5335
  have eq5424 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5304 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq5304
    | (have j0 := eq5304 X0 X1
       grind)
    | exact resolve eq5304 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5304
  have eq5473 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq5424 X1 X0
       grind)
    | exact superpose eq5424 eq11
    | (have j1 := eq5424 X1 X0
       grind)
    | exact resolve eq11 eq5424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5424
  have eq5597 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5473 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq5473
    | (have j0 := eq5473 X0 X1
       grind)
    | exact resolve eq5473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5473
  have eq5632 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq5597 (τ X0) X1
       grind)
    | exact superpose eq5597 eq19
    | (have j1 := eq5597 (τ X0) X1
       grind)
    | exact resolve eq19 eq5597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq5597
  have eq5756 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5416 (τ X1) X0
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq5416
    | (have j0 := eq5416 (τ X0) X1
       grind)
    | exact resolve eq5416 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq5416
  have eq5884 : ∀ X0 X1 : G, X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5756 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5756
    | (have j0 := eq5756 X0 X1
       grind)
    | exact resolve eq5756 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5756
  have eq5922 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5884 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5884
    | (have j0 := eq5884 X0 X1
       grind)
    | exact resolve eq5884 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5884
  have eq6053 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq5922 X1 X0
       grind)
    | exact superpose eq5922 eq11
    | (have j1 := eq5922 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq5922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5922
  have eq6179 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6053 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq6053
    | (have j0 := eq6053 X0 X1
       grind)
    | exact resolve eq6053 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6053
  have eq6267 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6179 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6179
    | (have j0 := eq6179 (τ (σ X0)) (τ (σ (k X0 X1)))
       grind)
    | exact resolve eq6179 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6179
  have eq6444 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6267 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq6267
    | (have j0 := eq6267 X0 X1
       grind)
    | exact resolve eq6267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6267
  have eq6449 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6444 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6444
    | (have j0 := eq6444 X0 X1
       grind)
    | exact resolve eq6444 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6444
  have eq6862 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5632 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5632
    | exact resolve eq5632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5632
  have eq6944 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6862 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6862
    | (have j0 := eq6862 X0 X1
       grind)
    | exact resolve eq6862 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6862
  have eq7262 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6449 y x
       grind)
    | exact superpose eq6449 eq16
    | (have j1 := eq6449 x y
       grind)
    | exact resolve eq16 eq6449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6449
  have eq7302 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq7262
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq7262
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq7262
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq7262
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq7262 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7303 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq7262
       have i₂ := eq6944 x y
       grind)
    | exact superpose eq6944 eq7262
    | (have j1 := eq6944 x y
       grind)
    | (have r₁ := eq7262
       have r₂ := eq6944 x y
       grind)
    | (have r₁ := eq7262
       have r₂ := eq6944 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq7262
       have r₂ := eq6944 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq7262 eq6944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6944 eq7262
  have eq7306 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by grind
  clear eq7303
  have eq7307 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq7306
  have eq7308 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq7302
  have eq7309 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7308
  have eq7312 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7307
       grind)
    | exact superpose eq7307 eq16
    | exact resolve eq16 eq7307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7307
  have eq7313 : y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7312
       have r₂ := eq22 x
       grind)
    | exact resolve eq7312 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7312
  have eq7323 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3375 x y
       have i₂ := eq7313
       grind)
    | exact superpose eq7313 eq3375
    | (have j0 := eq3375 x y
       grind)
    | exact resolve eq3375 eq7313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3375 eq7313
  have eq7330 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq7323
  have eq7331 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq7330
  have eq7345 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7331
       grind)
    | exact superpose eq7331 eq16
    | exact resolve eq16 eq7331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7331
  have eq7366 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq7345
       have i₂ := eq7309
       grind)
    | exact superpose eq7309 eq7345
    | exact resolve eq7345 eq7309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7309 eq7345
  have eq7367 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7366
  have eq7368 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq7367
  have eq7369 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7368
       grind)
    | exact superpose eq7368 eq16
    | exact resolve eq16 eq7368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7368
  have eq7370 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq7369
       have r₂ := eq22 x
       grind)
    | exact resolve eq7369 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7369
  have eq7371 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7370
       grind)
    | exact superpose eq7370 eq16
    | exact resolve eq16 eq7370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7372 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7370
       grind)
    | exact superpose eq7370 eq10
    | exact resolve eq10 eq7370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7370
  have eq7434 : x = y := by
    first
    | (have i₁ := eq7372
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7372
    | exact resolve eq7372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7372
  have eq7435 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7371
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq7371
    | exact resolve eq7371 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq7371
  have eq7436 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7435
       have i₂ := eq7434
       grind)
    | exact superpose eq7434 eq7435
    | exact resolve eq7435 eq7434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7434 eq7435
  have eq7437 : False := by grind
  exact eq7437

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq81 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
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
  have eq85 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq85
    | (have j0 := eq85 X0
       grind)
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq85
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | (have j0 := eq92 X0
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq93 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq93 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq97 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq94 (σ X0)
       grind)
    | exact superpose eq94 eq15
    | exact resolve eq15 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq97
    | exact resolve eq97 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq97
  have eq248 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq581 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81
    | exact resolve eq81 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq617 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq581 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq581
    | (have j0 := eq581 X0 X1
       grind)
    | exact resolve eq581 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq838 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq248
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq248
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq248
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq248
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq248 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq839 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq838
  have eq7824 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq839
       grind)
    | exact superpose eq839 eq16
    | exact resolve eq16 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq7825 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq7824
       have r₂ := eq108 x
       grind)
    | exact resolve eq7824 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7824
  have eq7937 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq7825
       grind)
    | exact superpose eq7825 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq7825
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7825
       grind)
    | exact resolve eq12 eq7825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7825
  have eq7956 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq7937
  have eq7957 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq248
       have i₂ := eq7956
       grind)
    | exact superpose eq7956 eq248
    | exact resolve eq248 eq7956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq7956
  have eq7973 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq7957
  have eq7974 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq7973
  have eq8091 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq7974
       grind)
    | exact superpose eq7974 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7974
       grind)
    | exact resolve eq12 eq7974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7974
  have eq8111 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8091
  have eq8117 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8111
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq8111
    | exact resolve eq8111 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8111
  have eq8123 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8117
       grind)
    | exact superpose eq8117 eq16
    | exact resolve eq16 eq8117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8117
  have eq8424 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq8123
       have i₂ := eq617 x y
       grind)
    | exact superpose eq617 eq8123
    | (have j1 := eq617 x y
       grind)
    | (have r₁ := eq8123
       have r₂ := eq617 x y
       grind)
    | (have r₁ := eq8123
       have r₂ := eq617 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8123
       have r₂ := eq617 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8123 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq8425 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq8424
  have eq8429 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8425
       grind)
    | exact superpose eq8425 eq16
    | exact resolve eq16 eq8425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8425
  have eq8430 : y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8429
       have r₂ := eq108 x
       grind)
    | exact resolve eq8429 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8429
  have eq8589 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq8430
       grind)
    | exact superpose eq8430 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8430
       grind)
    | exact resolve eq12 eq8430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8430
  have eq8609 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq8589
  have eq8610 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8123
       have i₂ := eq8609
       grind)
    | exact superpose eq8609 eq8123
    | exact resolve eq8123 eq8609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8123 eq8609
  have eq8629 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq8610
  have eq8630 : (σ x) = (σ y) := by grind
  clear eq8629
  have eq8782 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8630
       grind)
    | exact superpose eq8630 eq16
    | exact resolve eq16 eq8630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8783 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8630
       grind)
    | exact superpose eq8630 eq10
    | exact resolve eq10 eq8630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8630
  have eq8857 : x = y := by
    first
    | (have i₁ := eq8783
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8783
    | exact resolve eq8783 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8783
  have eq8858 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8782
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq8782
    | exact resolve eq8782 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq8782
  have eq8863 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8858
       have i₂ := eq8857
       grind)
    | exact superpose eq8857 eq8858
    | exact resolve eq8858 eq8857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8857 eq8858
  have eq8864 : False := by grind
  exact eq8864

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq40 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq77 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq236 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq16
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq940 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq245 (τ X0) (τ X1)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq245
    | (have j0 := eq245 (τ X0) (τ X1)
       grind)
    | exact resolve eq245 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq940 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq940
    | (have j0 := eq940 X0 X1
       grind)
    | exact resolve eq940 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq961 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq955 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq955
    | (have j0 := eq955 X0 X1
       grind)
    | exact resolve eq955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq966 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq961 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq961
    | (have j0 := eq961 X0 X1
       grind)
    | exact resolve eq961 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq970 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq966 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq966
    | (have j0 := eq966 X0 X1
       grind)
    | exact resolve eq966 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq974 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq970 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq970
    | (have j0 := eq970 X0 X1
       grind)
    | exact resolve eq970 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq976 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq4249 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq77 X0 (σ X0)
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4281 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq4282 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4281 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4281
  have eq4284 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4249
  have eq4285 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4284 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4284
  have eq4287 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4282 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4282
    | (have j0 := eq4282 X0
       grind)
    | exact resolve eq4282 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4282
  have eq4387 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq4287 X0
       grind)
    | exact superpose eq4287 eq40
    | (have j1 := eq4287 X0
       grind)
    | exact resolve eq40 eq4287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4287
  have eq4411 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4387 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4387
    | (have j0 := eq4387 X0
       grind)
    | exact resolve eq4387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4387
  have eq4412 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4411 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4411
  have eq4414 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4412 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4412
    | exact resolve eq4412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4441 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4412 X0
       grind)
    | exact superpose eq4412 eq11
    | exact resolve eq11 eq4412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4502 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4414 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq4414
    | exact resolve eq4414 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4414
  have eq4578 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4502 X0
       grind)
    | exact superpose eq4502 eq11
    | exact resolve eq11 eq4502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4689 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4578 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4578
    | exact resolve eq4578 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578
  have eq4751 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq4689 (τ X0)
       grind)
    | exact superpose eq4689 eq36
    | exact resolve eq36 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4806 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4751 X0
       have i₂ := eq4502 X0
       grind)
    | exact superpose eq4502 eq4751
    | exact resolve eq4751 eq4502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4502 eq4751
  have eq5394 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5433 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5394 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5394
    | exact resolve eq5394 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5394
  have eq5468 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5433 X0
       have i₂ := eq4689 X0
       grind)
    | exact superpose eq4689 eq5433
    | exact resolve eq5433 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5433
  have eq5484 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5468
  have eq50857 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4285 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4285
    | exact resolve eq4285 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50961 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) X0
       have i₂ := eq4285 (σ X0) X1
       grind)
    | exact superpose eq4285 eq25
    | (have j1 := eq4285 (σ X0) X1
       grind)
    | exact resolve eq25 eq4285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4285
  have eq51056 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq50961 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq50961
    | (have j0 := eq50961 X0 X1
       grind)
    | exact resolve eq50961 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50961
  have eq51108 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50857 X0 X1
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq50857
    | (have j0 := eq50857 X0 X1
       grind)
    | exact resolve eq50857 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50857
  have eq51139 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51056 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51056
    | (have j0 := eq51056 X0 X1
       grind)
    | exact resolve eq51056 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51056
  have eq51213 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51139 X0 X1
       have i₂ := eq4441 X0
       grind)
    | exact superpose eq4441 eq51139
    | (have j0 := eq51139 X0 X1
       grind)
    | exact resolve eq51139 eq4441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51139
  have eq51259 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51213 X0 X1
       have i₂ := eq4689 X0
       grind)
    | exact superpose eq4689 eq51213
    | (have j0 := eq51213 X0 X1
       grind)
    | exact resolve eq51213 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51213
  have eq51296 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51259 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51259
    | (have j0 := eq51259 X0 X1
       grind)
    | exact resolve eq51259 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51259
  have eq52038 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq51108 X0 X1
       grind)
    | exact superpose eq51108 eq11
    | (have j1 := eq51108 X0 X1
       grind)
    | exact resolve eq11 eq51108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51108
  have eq52240 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52038 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq52038
    | (have j0 := eq52038 X0 X1
       grind)
    | exact resolve eq52038 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52038
  have eq52535 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq52240 (τ X0) X1
       grind)
    | exact superpose eq52240 eq18
    | (have j1 := eq52240 (τ X0) X1
       grind)
    | exact resolve eq18 eq52240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq52240
  have eq56920 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51296 (τ X0) (τ X1)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq51296
    | (have j0 := eq51296 (τ X1) (τ X0)
       grind)
    | exact resolve eq51296 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq51296
  have eq57299 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq56920 X0 X1
       have i₂ := eq4806 X1
       grind)
    | exact superpose eq4806 eq56920
    | (have j0 := eq56920 X0 X1
       grind)
    | exact resolve eq56920 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56920
  have eq57464 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq57299 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq57299
    | (have j0 := eq57299 X0 X1
       grind)
    | exact resolve eq57299 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57299
  have eq57595 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq57464 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57464
    | (have j0 := eq57464 X0 X1
       grind)
    | exact resolve eq57464 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57464
  have eq57708 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57595 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq57595
    | (have j0 := eq57595 X0 X1
       grind)
    | exact resolve eq57595 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57595
  have eq57795 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57708 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57708
    | (have j0 := eq57708 X0 X1
       grind)
    | exact resolve eq57708 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57708
  have eq58212 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq57795 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57795
  have eq63654 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (τ X1)
       have i₂ := eq52535 X1 (τ X0)
       grind)
    | exact superpose eq52535 eq19
    | (have j1 := eq52535 X1 (τ X0)
       grind)
    | exact resolve eq19 eq52535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq52535
  have eq63744 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63654 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq63654
    | (have j0 := eq63654 X0 X1
       grind)
    | exact resolve eq63654 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63654
  have eq63846 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63744 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63744
    | (have j0 := eq63744 X0 X1
       grind)
    | exact resolve eq63744 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63744
  have eq63926 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63846 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63846
    | (have j0 := eq63846 X0 X1
       grind)
    | exact resolve eq63846 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63846
  have eq63998 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63926 X0 X1
       have i₂ := eq4806 X0
       grind)
    | exact superpose eq4806 eq63926
    | (have j0 := eq63926 X0 X1
       grind)
    | exact resolve eq63926 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4806 eq63926
  have eq69998 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (τ (M.op X1 X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq63998 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63998
    | (have j0 := eq63998 X1 (σ X0)
       grind)
    | exact resolve eq63998 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63998
  have eq77256 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq69998 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq69998
    | (have j0 := eq69998 X0 (σ X1)
       grind)
    | exact resolve eq69998 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69998
  have eq77487 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq77256 X0 X1
       have i₂ := eq4412 X1
       grind)
    | exact superpose eq4412 eq77256
    | (have j0 := eq77256 X0 X1
       grind)
    | exact resolve eq77256 eq4412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4412 eq77256
  have eq77604 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq77487 X0 X1
       have i₂ := eq4689 X1
       grind)
    | exact superpose eq4689 eq77487
    | (have j0 := eq77487 X0 X1
       grind)
    | exact resolve eq77487 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77487
  have eq77710 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77604 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq77604
    | (have j0 := eq77604 X0 X1
       grind)
    | exact resolve eq77604 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77604
  have eq79088 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq236
       have i₂ := eq77710 x y
       grind)
    | exact superpose eq77710 eq236
    | (have j1 := eq77710 x y
       grind)
    | (have r₁ := eq236
       have r₂ := eq77710 x y
       grind)
    | exact resolve eq236 eq77710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq77710
  have eq79210 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq79088
  have eq79277 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq245 x y
       grind)
    | (have r₁ := eq79210
       have r₂ := eq245 x y
       grind)
    | exact resolve eq79210 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq79210
  have eq79417 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq79277
       have i₂ := eq4441 y
       grind)
    | exact superpose eq4441 eq79277
    | exact resolve eq79277 eq4441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79277
  have eq79513 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq79417
       have i₂ := eq4689 y
       grind)
    | exact superpose eq4689 eq79417
    | exact resolve eq79417 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79417
  have eq81820 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79513
       grind)
    | exact superpose eq79513 eq16
    | exact resolve eq16 eq79513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81870 : (τ (σ y)) ≠ (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq58212 (σ x) (σ y)
       have i₂ := eq79513
       grind)
    | exact superpose eq79513 eq58212
    | (have j0 := eq58212 (σ x) (σ y)
       grind)
    | exact resolve eq58212 eq79513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58212 eq79513
  have eq81873 : (σ x) = (M.op (σ y) (σ y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq81870
  have eq81878 : (σ x) = (σ (k y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81873
       have i₂ := eq4441 y
       grind)
    | exact superpose eq4441 eq81873
    | exact resolve eq81873 eq4441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4441 eq81873
  have eq81927 : (σ x) = (σ (M.op y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81878
       have i₂ := eq4689 y
       grind)
    | exact superpose eq4689 eq81878
    | exact resolve eq81878 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4689 eq81878
  have eq81928 : (σ x) = (σ (M.op y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ x = (M.op y y) := by grind
  clear eq81927
  have eq81971 : (τ (σ y)) = (k (τ (σ x)) y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81928
       have i₂ := eq25 (σ x) y
       grind)
    | exact superpose eq25 eq81928
    | exact resolve eq81928 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq81928
  have eq81991 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81971
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq81971
    | exact resolve eq81971 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81971
  have eq82006 : y = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81991
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq81991
    | exact resolve eq81991 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81991
  have eq83061 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq976 x y
       have i₂ := eq82006
       grind)
    | exact superpose eq82006 eq976
    | (have j0 := eq976 x y
       grind)
    | (have r₁ := eq976 x y
       have r₂ := eq82006
       grind)
    | exact resolve eq976 eq82006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976 eq82006
  have eq83071 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq83061
  have eq83072 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq83071
  have eq83965 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq81820
       have i₂ := eq83072
       grind)
    | exact superpose eq83072 eq81820
    | exact resolve eq81820 eq83072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81820 eq83072
  have eq83966 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq83965
  have eq83967 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq83966
  have eq83985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5484 y
       have i₂ := eq83967
       grind)
    | exact superpose eq83967 eq5484
    | exact resolve eq5484 eq83967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83967
  have eq84068 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq83985
       have r₂ := eq16
       grind)
    | exact resolve eq83985 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83985
  have eq85076 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq84068
       grind)
    | exact superpose eq84068 eq10
    | exact resolve eq10 eq84068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84068
  have eq85261 : x = (M.op y y) := by
    first
    | (have i₁ := eq85076
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq85076
    | exact resolve eq85076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85076
  have eq85384 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5484 y
       have i₂ := eq85261
       grind)
    | exact superpose eq85261 eq5484
    | exact resolve eq5484 eq85261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5484 eq85261
  have eq85472 : False := by grind
  exact eq85472

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxy_pxx_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq23 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
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
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
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
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq40 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq47 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq42
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq49 X0 X1
       grind)
    | (have r₁ := eq50 X0 X1
       have r₂ := eq49 X0 X1
       grind)
    | exact resolve eq50 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq50
  have eq161 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq165 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq161 X0 X1
       have j1 := eq53 X0 X1
       grind)
    | (have r₁ := eq161 X0 X1
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq161 X1 X1
       have r₂ := eq53 X1 X1
       grind)
    | exact resolve eq161 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq161
  have eq426 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq165 (σ X0) (σ X1)
       grind)
    | exact superpose eq165 eq15
    | exact resolve eq15 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq426 X0 X1
       have i₂ := eq165 X0 X1
       grind)
    | exact superpose eq165 eq426
    | exact resolve eq426 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq426
  have eq433 : False := by grind
  exact eq433

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyy_x_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
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
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq107 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq96
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq146 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq129
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq146
  have eq167 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq189 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq204 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq206 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X1 X2)) = (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X1 X2) X3 X1
       have i₂ := eq53 X1 X0 X2
       grind)
    | (have i₁ := eq53 (M.op X1 X1) X1 X0
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 X1 X3 x
       have i₂ := eq53 X1 X0 x
       grind)
    | (have i₁ := eq53 X0 X1 X0
       have i₂ := eq53 X0 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) X0) x X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 x X2
       have i₂ := eq53 X0 x X1
       grind)
    | (have i₁ := eq53 X2 X2 X2
       have i₂ := eq53 X2 X1 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 x
       have i₂ := eq53 X1 X0 x
       grind)
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq53 X0 X0 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq209 sF2
       have i₂ := eq53 sF2 x sF2
       grind)
    | (have i₁ := eq209 x
       have i₂ := eq53 sF2 x x
       grind)
    | exact superpose eq53 eq209
    | exact resolve eq209 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq820 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq353 sF0
       have i₂ := eq53 sF0 x x
       grind)
    | exact superpose eq53 eq353
    | exact resolve eq353 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq843 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq354 eq53
    | exact resolve eq53 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq342 X3 X1 x
       have i₂ := eq342 X0 X1 x
       grind)
    | (have i₁ := eq342 X0 X1 X3
       have i₂ := eq342 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq342 eq342
    | exact resolve eq342 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1083 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq342 X0 (M.op X1 X1) X3
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq342 X0 (M.op X1 X1) X3
       have i₂ := eq342 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq342 eq342
    | exact resolve eq342 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1112 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq51 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq51
    | exact resolve eq51 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1118 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (M.op X1 X1)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq209 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq209
    | exact resolve eq209 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1123 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq820 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq820 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq820
    | exact resolve eq820 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq1168 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1083 X0 X1 x X3
       have i₂ := eq52 X0 x X1
       grind)
    | exact superpose eq52 eq1083
    | exact resolve eq1083 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1083
  have eq2866 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq352 X0 X1 (M.op X0 X1)
       have i₂ := eq356 (M.op X0 X1) X2 X0
       grind)
    | (have i₁ := eq352 X0 X1 (M.op X0 X1)
       have i₂ := eq356 (M.op X0 X1) X0 X2
       grind)
    | exact superpose eq356 eq352
    | exact resolve eq352 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq2868 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op (M.op X1 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq352 X1 X2 (M.op X1 X2)
       have i₂ := eq53 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq53 eq352
    | exact resolve eq352 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq352
  have eq3388 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq354 eq345
    | exact resolve eq345 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq354
  have eq3605 : ∀ X1 X2 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ x)) := by
    intro X1 X2
    first
    | exact superpose eq209 eq3388
    | exact resolve eq3388 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq3388
  have eq4552 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq167
    | (have j0 := eq167 x
       grind)
    | exact resolve eq167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq4563 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4552
  have eq4567 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4563
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq4563
    | exact resolve eq4563 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq4563
  have eq4583 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq4567
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq4567 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4567
  have eq4589 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq4583 eq49
    | exact resolve eq49 eq4583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq4775 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq189 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq189
    | (have j0 := eq189 y
       grind)
    | exact resolve eq189 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq4785 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4775
  have eq4788 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4785
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq4785
    | exact resolve eq4785 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4785
  have eq4810 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4788
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq4788 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4788
  have eq4824 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4810 eq84
    | exact resolve eq84 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq5015 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq204
    | (have j0 := eq204 (M.op x y)
       grind)
    | exact resolve eq204 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq5024 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5015
  have eq5026 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq129 eq5024
    | exact resolve eq5024 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5024
  have eq5052 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq5026
       have r₂ := eq13 x (σ (M.op x y))
       grind)
    | exact resolve eq5026 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5026
  have eq5070 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5052 eq152
    | exact resolve eq152 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq12623 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4810 eq106
    | exact resolve eq106 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq12715 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4583 eq107
    | exact resolve eq107 eq4583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq4583
  have eq13531 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5052 eq153
    | exact resolve eq153 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq17363 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq12623
       grind)
    | exact superpose eq12623 eq16
    | exact resolve eq16 eq12623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12623
  have eq17416 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4824 eq17363
    | exact resolve eq17363 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17363
  have eq17419 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq17416
       have r₂ := eq13 x y
       grind)
    | exact resolve eq17416 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17416
  have eq17420 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq17419
       grind)
    | exact superpose eq17419 eq70
    | exact resolve eq70 eq17419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq17455 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4810 eq17420
    | exact resolve eq17420 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4810 eq17420
  have eq17521 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq12715
       grind)
    | exact superpose eq12715 eq16
    | exact resolve eq16 eq12715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12715
  have eq17576 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4589 eq17521
    | exact resolve eq17521 eq4589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17521
  have eq17579 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq17576
       have r₂ := eq13 x x
       grind)
    | exact resolve eq17576 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17576
  have eq18368 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13531 eq16
    | exact resolve eq16 eq13531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13531
  have eq18427 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5070 eq18368
    | exact resolve eq18368 eq5070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5070 eq18368
  have eq18430 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq18427
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq18427 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18427
  have eq18431 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq18430 eq129
    | exact resolve eq129 eq18430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq18430
  have eq18466 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq5052 eq18431
    | exact resolve eq18431 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5052 eq18431
  have eq24188 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq24189 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq24188
    | exact resolve eq24188 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24188
  have eq24200 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq24189
       have r₂ := eq27
       grind)
    | exact resolve eq24189 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24189
  have eq24204 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq24200 eq4824
    | exact resolve eq4824 eq24200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24200
  have eq24286 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq24204
       have i₂ := eq17419
       grind)
    | exact superpose eq17419 eq24204
    | exact resolve eq24204 eq17419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24204
  have eq24295 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq24286
    | exact resolve eq24286 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24286
  have eq24296 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq24295
  have eq24300 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq24296 eq14
    | exact resolve eq14 eq24296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24399 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24300 eq1112
    | exact resolve eq1112 eq24300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq24402 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24300 eq1118
    | exact resolve eq1118 eq24300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq24445 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq24300 eq1072
    | exact resolve eq1072 eq24300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24300
  have eq24708 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24402 eq24399
    | exact resolve eq24399 eq24402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24399 eq24402
  have eq24723 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq24708
  have eq25564 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq24445
    | (have j0 := eq24445 (σ x) X0
       grind)
    | exact resolve eq24445 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24445
  have eq27063 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24296 eq24723
    | exact resolve eq24723 eq24296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24296 eq24723
  have eq27078 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq27063
  have eq27101 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27078 eq25564
    | exact resolve eq25564 eq27078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25564 eq27078
  have eq27173 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq27101
  have eq27217 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq17455
       have i₂ := eq27173
       grind)
    | exact superpose eq27173 eq17455
    | exact resolve eq17455 eq27173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27252 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq1072 X0 y x
       have i₂ := eq27173
       grind)
    | exact superpose eq27173 eq1072
    | exact resolve eq1072 eq27173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27173
  have eq27291 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq27217
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27217
    | exact resolve eq27217 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27217
  have eq27535 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq27291 eq1072
    | exact resolve eq1072 eq27291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27291
  have eq29286 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq27252 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27252
    | (have j0 := eq27252 x X0
       grind)
    | exact resolve eq27252 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27252
  have eq29936 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq17455
       have i₂ := eq29286 y
       grind)
    | exact superpose eq29286 eq17455
    | exact resolve eq17455 eq29286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29286
  have eq29966 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq29936
    | exact resolve eq29936 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29936
  have eq32678 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq27535
    | (have j0 := eq27535 (σ x) X0
       grind)
    | exact resolve eq27535 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27535
  have eq33209 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32678 eq29966
    | exact resolve eq29966 eq32678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29966 eq32678
  have eq33212 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq33209
  have eq33242 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq33212
       have r₂ := eq27
       grind)
    | exact resolve eq33212 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33212
  have eq33542 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq33242
       grind)
    | exact superpose eq33242 eq14
    | exact resolve eq14 eq33242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33242
  have eq34020 : ∀ X0 : G, y = (M.op X0 (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq33542 x
       have i₂ := eq342 X0 y x
       grind)
    | (have i₁ := eq33542 X0
       have i₂ := eq342 (M.op X0 X0) y x
       grind)
    | exact superpose eq342 eq33542
    | exact resolve eq33542 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq34121 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1072 X0 (M.op y y) x
       have i₂ := eq33542 y
       grind)
    | exact superpose eq33542 eq1072
    | exact resolve eq1072 eq33542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33542
  have eq34748 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34121 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34121
    | (have j0 := eq34121 x X0
       grind)
    | exact resolve eq34121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34121
  have eq35236 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17455
       have i₂ := eq34748 y
       grind)
    | exact superpose eq34748 eq17455
    | exact resolve eq17455 eq34748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17455
  have eq35247 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34020 X0
       have i₂ := eq34748 y
       grind)
    | exact superpose eq34748 eq34020
    | exact resolve eq34020 eq34748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34020 eq34748
  have eq35256 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq35247 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35247
  have eq35276 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq35236
    | exact resolve eq35236 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35236
  have eq35669 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35256 eq18466
    | exact resolve eq18466 eq35256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18466 eq35256
  have eq35689 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35669
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35669
    | exact resolve eq35669 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq35669
  have eq36017 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq35276 eq1168
    | exact resolve eq1168 eq35276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq35276
  have eq43705 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq35689 eq36017
    | exact resolve eq36017 eq35689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35689 eq36017
  have eq43924 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq43705 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43705
  have eq44476 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43924 eq26
    | (have j1 := eq43924 (σ x)
       grind)
    | exact resolve eq26 eq43924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43924
  have eq44523 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq44476
       have r₂ := eq27
       grind)
    | exact resolve eq44476 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44476
  have eq44537 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq44523 eq27
    | exact resolve eq27 eq44523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq44551 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ x)) X1)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq44523 eq3605
    | exact resolve eq3605 eq44523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3605
  have eq44561 : ∀ X1 : G, (M.op (σ x) (σ x)) = (M.op X1 (σ x)) := by
    intro X1
    first
    | (have i₁ := eq44551 x X1
       have i₂ := eq357 sF2 X1 x
       grind)
    | exact superpose eq357 eq44551
    | exact resolve eq44551 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44551
  have eq45193 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op (M.op (σ x) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq44561 eq843
    | exact resolve eq843 eq44561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq45194 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq45193 x x
       have i₂ := eq357 sF2 x x
       grind)
    | exact superpose eq357 eq45193
    | exact resolve eq45193 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq45193
  have eq45749 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45194 X1
       have i₂ := eq350 sF2 X1 x
       grind)
    | (have i₁ := eq45194 X1
       have i₂ := eq350 X0 X1 sF2
       grind)
    | exact superpose eq350 eq45194
    | exact resolve eq45194 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq45766 : (M.op (M.op x y) x) = (M.op (σ x) x) := by
    first
    | exact superpose eq50 eq45194
    | exact resolve eq45194 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45194
  have eq45908 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (M.op (M.op x y) x)) (M.op (M.op (M.op x y) x) (σ x))) := by
    intro X0
    first
    | exact superpose eq45766 eq2868
    | exact resolve eq2868 eq45766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2868 eq45766
  have eq45923 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (M.op (M.op x y) x)) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq44561 eq45908
    | exact resolve eq45908 eq44561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45908
  have eq45939 : (σ x) = (M.op x (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq50 eq45923
    | exact resolve eq45923 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq45923
  have eq46005 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq45939
       have i₂ := eq1072 x sF2 x
       grind)
    | (have i₁ := eq45939
       have i₂ := eq1072 X0 sF2 x
       grind)
    | exact superpose eq1072 eq45939
    | exact resolve eq45939 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45939
  have eq48767 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq46005 eq45749
    | exact resolve eq45749 eq46005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45749
  have eq49031 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq48767
    | (have j0 := eq48767 (σ y)
       grind)
    | exact resolve eq48767 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq48767
  have eq49135 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq44523 eq49031
    | exact resolve eq49031 eq44523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44523 eq49031
  have eq49154 : (τ (σ y)) = (k x x) := by
    first
    | exact superpose eq49135 eq4589
    | exact resolve eq4589 eq49135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4589
  have eq49168 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq49135 eq46005
    | exact resolve eq46005 eq49135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49302 : (τ (σ y)) = (M.op x x) := by
    first
    | (have i₁ := eq49154
       have i₂ := eq17579
       grind)
    | exact superpose eq17579 eq49154
    | exact resolve eq49154 eq17579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17579 eq49154
  have eq49319 : y = (M.op x x) := by
    first
    | exact superpose eq29 eq49302
    | exact resolve eq49302 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq49302
  have eq49594 : (τ (σ x)) = (k y y) := by
    first
    | exact superpose eq49168 eq4824
    | exact resolve eq4824 eq49168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4824 eq49168
  have eq49627 : (τ (σ x)) = (M.op y y) := by
    first
    | (have i₁ := eq49594
       have i₂ := eq17419
       grind)
    | exact superpose eq17419 eq49594
    | exact resolve eq49594 eq17419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17419 eq49594
  have eq49668 : x = (M.op y y) := by
    first
    | exact superpose eq28 eq49627
    | exact resolve eq49627 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq49627
  have eq49782 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1072 X0 x x
       have i₂ := eq49319
       grind)
    | exact superpose eq49319 eq1072
    | exact resolve eq1072 eq49319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq49967 : (M.op (M.op x y) x) = (M.op x x) := by
    first
    | (have i₁ := eq206 y
       have i₂ := eq49668
       grind)
    | exact superpose eq49668 eq206
    | exact resolve eq206 eq49668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq49668
  have eq50085 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq49967
       have i₂ := eq49319
       grind)
    | exact superpose eq49319 eq49967
    | exact resolve eq49967 eq49319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49319 eq49967
  have eq50323 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) X1) (σ x)) (M.op (σ x) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq46005 eq2866
    | exact resolve eq2866 eq46005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2866 eq46005
  have eq50771 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq378 eq50323
    | (have j0 := eq50323 X0 (σ y)
       grind)
    | exact resolve eq50323 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq50323
  have eq50836 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq44561 eq50771
    | exact resolve eq50771 eq44561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44561 eq50771
  have eq50854 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq49135 eq50836
    | exact resolve eq50836 eq49135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49135 eq50836
  have eq51568 : x = (M.op (M.op (σ x) (M.op x y)) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq50854 eq1123
    | exact resolve eq1123 eq50854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123 eq50854
  have eq51630 : x = (M.op (M.op (σ x) (M.op x y)) y) := by
    first
    | exact superpose eq50085 eq51568
    | exact resolve eq51568 eq50085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50085 eq51568
  have eq52480 : ∀ X0 : G, x = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq51630 eq49782
    | exact resolve eq49782 eq51630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49782 eq51630
  have eq53055 : x = (M.op x y) := by
    first
    | (have i₁ := eq52480 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52480
    | (have j0 := eq52480 x
       grind)
    | exact resolve eq52480 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq52480
  have eq53346 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq53055 eq20
    | exact resolve eq20 eq53055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq53055
  have eq53561 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq53346
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq53346
    | exact resolve eq53346 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq53346
  have eq53633 : False := by grind
  exact eq53633

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  have eq53 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
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
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq86 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 : G, (σ x) = (M.op (σ (M.op X0 X0)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq54
    | exact resolve eq54 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq214 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq214
    | exact resolve eq214 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq214
  have eq494 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq56 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op (M.op X0 X1) X0) x X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq56
  have eq1253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1254 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1253
    | exact resolve eq1253 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1257 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1254
       have r₂ := eq28
       grind)
    | exact resolve eq1254 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq1259 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1257
    | exact resolve eq1257 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1261 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1259 eq28
    | exact resolve eq28 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1262 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1259 eq54
    | exact resolve eq54 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1263 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1259 eq86
    | (have r₁ := eq86
       have r₂ := eq1259
       grind)
    | exact resolve eq86 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1267 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1263
  have eq1268 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1267
  have eq1335 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1268 eq77
    | exact resolve eq77 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1268
  have eq1339 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1335
  have eq1554 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq494 X3 X1 x
       have i₂ := eq494 X0 X1 x
       grind)
    | (have i₁ := eq494 X0 X1 X3
       have i₂ := eq494 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq494 eq494
    | exact resolve eq494 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1566 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq494 X0 (M.op X1 X1) X3
       have i₂ := eq494 X0 X1 X1
       grind)
    | (have i₁ := eq494 X0 (M.op X1 X1) X3
       have i₂ := eq494 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq494 eq494
    | exact resolve eq494 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1677 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1566 X0 X1 x X3
       have i₂ := eq55 X0 x X1
       grind)
    | exact superpose eq55 eq1566
    | exact resolve eq1566 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1566
  have eq3599 : (M.op x y) = (M.op x (M.op (M.op (M.op x y) x) (M.op x y))) := by
    first
    | exact superpose eq513 eq512
    | exact resolve eq512 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq513
  have eq3757 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1262 x
       have i₂ := eq494 X0 sF2 x
       grind)
    | (have i₁ := eq1262 X0
       have i₂ := eq494 (M.op X0 X0) sF2 x
       grind)
    | exact superpose eq494 eq1262
    | exact resolve eq1262 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq3781 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1262 eq14
    | exact resolve eq14 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9925 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4, g5, g6⟩ := hcon
    have f9925_18 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
      intro X0 X1
      grind
    have f9925_19 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
      intro X0
      grind
    have f9925_28 : X0 ≠ (M.op (σ x) (M.op (σ x) X0)) := by grind
    have f9925_32 : (σ x) ≠ (σ y) := by grind
    have f9925_33 : x ≠ (M.op x y) := by grind
    have f9925_34 : x ≠ y := by grind
    have f9925_36 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = y := by
      intro X0
      first
      | (have j0 := f9925_19 X0
         grind)
      | (have r₁ := f9925_19 X0
         have r₂ := f9925_32
         grind)
      | exact resolve f9925_19 f9925_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f9925_37 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ x = (M.op x y) ∨ x = y := by
      intro X0 X1
      first
      | (have j0 := f9925_18 X0 X1
         grind)
      | (have r₁ := f9925_18 X0 X1
         have r₂ := f9925_32
         grind)
      | exact resolve f9925_18 f9925_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f9925_38 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = y := by
      intro X0
      first
      | (have j0 := f9925_36 X0
         grind)
      | (have r₁ := f9925_36 X0
         have r₂ := f9925_33
         grind)
      | exact resolve f9925_36 f9925_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f9925_39 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ x = y := by
      intro X0 X1
      first
      | (have j0 := f9925_37 X0 X1
         grind)
      | (have r₁ := f9925_37 X0 X1
         have r₂ := f9925_33
         grind)
      | exact resolve f9925_37 f9925_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f9925_40 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
      intro X0
      first
      | (have j0 := f9925_38 X0
         grind)
      | (have r₁ := f9925_38 X0
         have r₂ := f9925_34
         grind)
      | exact resolve f9925_38 f9925_34
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f9925_41 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 := by
      intro X0 X1
      first
      | (have j0 := f9925_39 X0 X1
         grind)
      | (have r₁ := f9925_39 X0 X1
         have r₂ := f9925_34
         grind)
      | exact resolve f9925_39 f9925_34
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f9925_48 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 := by
      intro X0
      first
      | (have i₁ := f9925_41 X0 (M.op (σ x) (σ x))
         have i₂ := f9925_40 X0
         grind)
      | exact superpose f9925_40 f9925_41
      | exact resolve f9925_41 f9925_40
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f9925_61 : X0 ≠ X0 := by
      first
      | (have i₁ := f9925_28
         have i₂ := f9925_48 X0
         grind)
      | exact superpose f9925_48 f9925_28
      | (have r₁ := f9925_28
         have r₂ := f9925_48 X0
         grind)
      | exact resolve f9925_28 f9925_48
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f9925_64 : False := by grind
    exact f9925_64
  clear eq3757 eq3781
  have eq10203 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq9925 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9925
  have eq10256 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq10203
    | (have j0 := eq10203 (σ y)
       grind)
    | exact resolve eq10203 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10203
  have eq10300 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1259 eq10256
    | exact resolve eq10256 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259 eq10256
  have eq10316 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq10300
  have eq10406 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10316 eq1262
    | exact resolve eq1262 eq10316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262 eq10316
  have eq10418 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq10406
  have eq10456 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10418 eq1339
    | exact resolve eq1339 eq10418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339 eq10418
  have eq10518 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10456
  have eq10535 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10518
       have r₂ := eq1261
       grind)
    | exact resolve eq10518 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261 eq10518
  have eq10539 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq10535 eq30
    | exact resolve eq30 eq10535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10535
  have eq10559 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq10539
    | exact resolve eq10539 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10539
  have eq10560 : x = (M.op x y) ∨ x = y := by grind
  clear eq10559
  have eq10563 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq10560 eq21
    | exact resolve eq21 eq10560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10585 : x = (M.op x (M.op (M.op x x) x)) ∨ x = y := by
    first
    | exact superpose eq10560 eq3599
    | exact resolve eq3599 eq10560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3599
  have eq10591 : x = (M.op x (M.op (M.op x y) x)) ∨ x = y := by
    first
    | (have i₁ := eq10585
       have i₂ := eq211 x
       grind)
    | exact superpose eq211 eq10585
    | exact resolve eq10585 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq10585
  have eq10604 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq10563
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10563
    | exact resolve eq10563 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10563
  have eq10818 : x = (M.op x (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq10560 eq10591
    | exact resolve eq10591 eq10560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10591
  have eq10836 : x = (M.op x (M.op x x)) ∨ x = y := by grind
  clear eq10818
  have eq11648 : ∀ X0 : G, x = (M.op X0 (M.op x x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1554 x x X0
       have i₂ := eq10836
       grind)
    | exact superpose eq10836 eq1554
    | exact resolve eq1554 eq10836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq12749 : ∀ X0 : G, (M.op x x) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1677 x x X0
       have i₂ := eq10836
       grind)
    | exact superpose eq10836 eq1677
    | exact resolve eq1677 eq10836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677 eq10836
  have eq12927 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op x x) X1
       have i₂ := eq11648 (M.op x x)
       grind)
    | exact superpose eq11648 eq14
    | exact resolve eq14 eq11648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12938 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq375 (M.op x x)
       have i₂ := eq11648 (M.op x x)
       grind)
    | exact superpose eq11648 eq375
    | exact resolve eq375 eq11648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq12944 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq383 (M.op x x)
       have i₂ := eq11648 (M.op x x)
       grind)
    | exact superpose eq11648 eq383
    | exact resolve eq383 eq11648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq13055 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq12944
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12944
    | exact resolve eq12944 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12944
  have eq13059 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq12938
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12938
    | exact resolve eq12938 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12938
  have eq13212 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq52
       have i₂ := eq12749 X0
       grind)
    | (have i₁ := eq52
       have i₂ := eq12749 x
       grind)
    | exact superpose eq12749 eq52
    | exact resolve eq52 eq12749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq12749
  have eq14185 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq13055 eq13059
    | exact resolve eq13059 eq13055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13055 eq13059
  have eq14209 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y := by grind
  clear eq14185
  have eq31135 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12927 X0 (M.op x x)
       have i₂ := eq11648 X0
       grind)
    | exact superpose eq11648 eq12927
    | exact resolve eq12927 eq11648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11648 eq12927
  have eq31634 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq31135 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31135
  have eq31764 : y = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq31634 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq31634
    | (have j0 := eq31634 y
       grind)
    | exact resolve eq31634 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31634
  have eq31892 : y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq10560 eq31764
    | exact resolve eq31764 eq10560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10560 eq31764
  have eq31910 : y = (M.op x x) ∨ x = y := by grind
  clear eq31892
  have eq31937 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq13212 x
       have i₂ := eq31910
       grind)
    | exact superpose eq31910 eq13212
    | exact resolve eq13212 eq31910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13212 eq31910
  have eq32022 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq31937
  have eq32050 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq32022
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32022
    | exact resolve eq32022 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32022
  have eq32857 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq32050 eq14209
    | exact resolve eq14209 eq32050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14209 eq32050
  have eq32979 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq32857
  have eq33012 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq32979
    | exact resolve eq32979 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32979
  have eq33113 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq33012 eq28
    | exact resolve eq28 eq33012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33012
  have eq33174 : x = y := by
    first
    | (have r₁ := eq33113
       have r₂ := eq10604
       grind)
    | exact resolve eq33113 eq10604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10604 eq33113
  have eq33175 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq33174
       grind)
    | exact superpose eq33174 eq19
    | exact resolve eq19 eq33174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq33176 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq33174
       grind)
    | exact superpose eq33174 eq25
    | exact resolve eq25 eq33174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq33174
  have eq33285 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq33176
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33176
    | exact resolve eq33176 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq33176
  have eq33302 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq33285 eq27
    | exact resolve eq27 eq33285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq33285
  have eq33632 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq33302 eq68
    | exact resolve eq68 eq33302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq33302
  have eq33745 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq33632
       have i₂ := eq33175
       grind)
    | exact superpose eq33175 eq33632
    | exact resolve eq33632 eq33175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33175 eq33632
  have eq33753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33745 eq15
    | exact resolve eq15 eq33745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33745
  have eq33812 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq33753
    | exact resolve eq33753 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq33753
  have eq33826 : False := by grind
  exact eq33826

/-- `Equation1833`: `x = (x ◇ (x ◇ x)) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation1833 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1833 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1833.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq50 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq95 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq270 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq273 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq669 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95
    | exact resolve eq95 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq709 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq669 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq669
    | (have j0 := eq669 X0 X1
       grind)
    | exact resolve eq669 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq816 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq273 (τ X0) (τ X1)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq273
    | (have j0 := eq273 (τ X0) (τ X1)
       grind)
    | exact resolve eq273 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq824 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq816 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq816
    | (have j0 := eq816 X0 X1
       grind)
    | exact resolve eq816 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq827 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq824 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq824
    | (have j0 := eq824 X0 X1
       grind)
    | exact resolve eq824 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq829 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq827 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq827
    | (have j0 := eq827 X0 X1
       grind)
    | exact resolve eq827 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq830 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq829
    | (have j0 := eq829 X0 X1
       grind)
    | exact resolve eq829 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq831 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq830 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq830
    | (have j0 := eq830 X0 X1
       grind)
    | exact resolve eq830 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq832 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq831 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq831
    | (have j0 := eq831 X0 X1
       grind)
    | exact resolve eq831 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq1064 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq270
       have i₂ := eq709 y x
       grind)
    | exact superpose eq709 eq270
    | (have j1 := eq709 (σ y) (σ x)
       grind)
    | (have r₁ := eq270
       have r₂ := eq709 y x
       grind)
    | (have r₁ := eq270
       have r₂ := eq709 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq270
       have r₂ := eq709 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq270 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq709
  have eq1065 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1064
  have eq6109 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1065
       grind)
    | exact superpose eq1065 eq16
    | exact resolve eq16 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq6110 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq6109
       have r₂ := eq22 x
       grind)
    | exact resolve eq6109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6109
  have eq6275 : x ≠ x ∨ x = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq6110
       grind)
    | exact superpose eq6110 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6110
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq6110
       grind)
    | exact resolve eq13 eq6110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6110
  have eq6277 : x = y ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6275
  have eq8921 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6277
       grind)
    | exact superpose eq6277 eq16
    | exact resolve eq16 eq6277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6277
  have eq8922 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq8921
       have r₂ := eq22 x
       grind)
    | exact resolve eq8921 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8921
  have eq9074 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq8922
       grind)
    | exact superpose eq8922 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8922
       grind)
    | exact resolve eq13 eq8922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8922
  have eq9076 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq9074
  have eq9077 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq9076
  have eq9080 : x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq9077
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq9077
    | exact resolve eq9077 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9077
  have eq9236 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq273 x y
       have i₂ := eq9080
       grind)
    | exact superpose eq9080 eq273
    | (have j0 := eq273 x y
       grind)
    | (have r₁ := eq273 x y
       have r₂ := eq9080
       grind)
    | exact resolve eq273 eq9080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9080
  have eq9260 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq9236
  have eq9261 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq9260
  have eq9266 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq273 x y
       grind)
    | (have r₁ := eq9261
       have r₂ := eq273 x y
       grind)
    | exact resolve eq9261 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq9261
  have eq9269 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9266
       grind)
    | exact superpose eq9266 eq16
    | exact resolve eq16 eq9266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9271 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq9266
       grind)
    | exact superpose eq9266 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq9266
       grind)
    | exact resolve eq13 eq9266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9266
  have eq9273 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq9271
  have eq9274 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq9273
  have eq9277 : (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq9274
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq9274
    | exact resolve eq9274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9274
  have eq9431 : y = (τ (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9277
       grind)
    | exact superpose eq9277 eq10
    | exact resolve eq10 eq9277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9277
  have eq9518 : x = y ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq9431
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9431
    | exact resolve eq9431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9431
  have eq9668 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9518
       grind)
    | exact superpose eq9518 eq16
    | exact resolve eq16 eq9518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9518
  have eq9669 : (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq9668
       have r₂ := eq22 x
       grind)
    | exact resolve eq9668 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9668
  have eq9681 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq9669
       grind)
    | exact superpose eq9669 eq10
    | exact resolve eq10 eq9669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9669
  have eq9769 : x = (k x y) := by
    first
    | (have i₁ := eq9681
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9681
    | exact resolve eq9681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9681
  have eq9949 : x ≠ x ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq832 x y
       have i₂ := eq9769
       grind)
    | exact superpose eq9769 eq832
    | (have j0 := eq832 x y
       grind)
    | (have r₁ := eq832 x y
       have r₂ := eq9769
       grind)
    | exact resolve eq832 eq9769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq9769
  have eq9964 : x = (M.op x y) ∨ x = y := by grind
  clear eq9949
  have eq9968 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9269
       have i₂ := eq9964
       grind)
    | exact superpose eq9964 eq9269
    | exact resolve eq9269 eq9964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9269 eq9964
  have eq9975 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq9968
  have eq10140 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9975
       grind)
    | exact superpose eq9975 eq16
    | exact resolve eq16 eq9975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9975
  have eq10145 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq10140
       have r₂ := eq22 x
       grind)
    | exact resolve eq10140 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10140
  have eq10146 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10145
       grind)
    | exact superpose eq10145 eq16
    | exact resolve eq16 eq10145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10147 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10145
       grind)
    | exact superpose eq10145 eq10
    | exact resolve eq10 eq10145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10145
  have eq10238 : x = y := by
    first
    | (have i₁ := eq10147
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10147
    | exact resolve eq10147 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10147
  have eq10239 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10146
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq10146
    | exact resolve eq10146 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10146
  have eq10240 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10239
       have i₂ := eq10238
       grind)
    | exact superpose eq10238 eq10239
    | exact resolve eq10239 eq10238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10238 eq10239
  have eq10241 : False := by grind
  exact eq10241

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
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
  clear eq40
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
  have eq175 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (M.op X0 X0)) := by
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
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 (M.op X0 (M.op X0 X1)) (M.op x x) X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X1 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x (M.op x y)) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq176 eq178
    | exact resolve eq178 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 X0 x X3
       have i₂ := eq178 X0 x X1
       grind)
    | (have i₁ := eq178 x x x
       have i₂ := eq178 x X1 x
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq176 eq542
    | exact resolve eq542 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq542
  have eq576 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq175 eq541
    | exact resolve eq541 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq541
  have eq577 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq540 X0 X1 x
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq540
    | exact resolve eq540 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq596 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq577 X0 x
       have i₂ := eq178 X0 x X1
       grind)
    | (have i₁ := eq577 x x
       have i₂ := eq178 x X1 x
       grind)
    | exact superpose eq178 eq577
    | exact resolve eq577 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq1007 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k X0 X1)) (M.op X2 X2)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1045 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
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
  have eq1052 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq1056 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1064 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1045
       grind)
    | exact superpose eq1045 eq41
    | exact resolve eq41 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1065 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1064
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1064
    | exact resolve eq1064 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1067 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1065
    | exact resolve eq1065 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1067 eq1052
    | exact resolve eq1052 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq1067
  have eq1084 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1077
       have r₂ := eq27
       grind)
    | exact resolve eq1077 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1095 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1084 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq1084
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1084
       grind)
    | exact resolve eq13 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1107 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1095 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1227 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1107 eq1084
    | exact resolve eq1084 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084 eq1107
  have eq1258 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1227
  have eq1313 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1258 eq153
    | exact resolve eq153 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1258
  have eq1316 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq1313
    | exact resolve eq1313 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1313
  have eq1319 : y = (M.op y y) := by
    first
    | (have j1 := eq1056 y
       grind)
    | (have r₁ := eq1316
       have r₂ := eq1056 y
       grind)
    | exact resolve eq1316 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1324 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq1319
       grind)
    | exact superpose eq1319 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1319
       grind)
    | exact resolve eq13 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1329 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq179 y
       have i₂ := eq1319
       grind)
    | exact superpose eq1319 eq179
    | exact resolve eq179 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1332 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq547 X0 X1 y
       have i₂ := eq1319
       grind)
    | exact superpose eq1319 eq547
    | exact resolve eq547 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq1341 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq1324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq1348 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1329
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1329
    | exact resolve eq1329 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1329
  have eq1360 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1348 eq576
    | exact resolve eq576 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq1372 : x = (k (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1360 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq1472 : y = (k y y) := by
    first
    | (have i₁ := eq1319
       have i₂ := eq1341 y
       grind)
    | exact superpose eq1341 eq1319
    | exact resolve eq1319 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319 eq1341
  have eq1580 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1472
       grind)
    | exact superpose eq1472 eq41
    | exact resolve eq41 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1472
  have eq1583 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1580
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1580
    | exact resolve eq1580 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1580
  have eq1588 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1583 eq1056
    | (have j0 := eq1056 (σ y)
       grind)
    | (have r₁ := eq1056 (σ y)
       have r₂ := eq1583
       grind)
    | exact resolve eq1056 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq1589 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1588
  have eq1602 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1589 eq178
    | exact resolve eq178 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1603 : (M.op x (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq1589 eq179
    | exact resolve eq179 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1604 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1589 eq181
    | exact resolve eq181 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1609 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1589 eq596
    | exact resolve eq596 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq1589
  have eq1624 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq1604
    | exact resolve eq1604 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1625 : (M.op x y) = (M.op x (σ y)) := by
    first
    | exact superpose eq1348 eq1603
    | exact resolve eq1603 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq1641 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1624 eq575
    | exact resolve eq575 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq1624
  have eq1928 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1609 eq16
    | exact resolve eq16 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1939 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) y) := by
    intro X0
    first
    | (have i₁ := eq1928 X0 x
       have i₂ := eq1332 (M.op (M.op X0 sF3) X0) x
       grind)
    | exact superpose eq1332 eq1928
    | exact resolve eq1928 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1928
  have eq1948 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq1609 eq1939
    | exact resolve eq1939 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609 eq1939
  have eq4896 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1372 eq38
    | exact resolve eq38 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1372
  have eq4902 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4896
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4896
    | exact resolve eq4896 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4896
  have eq5084 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq4902 eq1007
    | (have j0 := eq1007 X0 (σ x) x
       grind)
    | exact resolve eq1007 eq4902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq5085 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5084 x
       have i₂ := eq1332 (M.op sF1 sF2) x
       grind)
    | exact superpose eq1332 eq5084
    | exact resolve eq5084 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5084
  have eq5089 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5085
       have i₂ := eq1948 (M.op sF1 sF2)
       grind)
    | exact superpose eq1948 eq5085
    | exact resolve eq5085 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5085
  have eq5091 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq5089
    | (have j1 := eq28 x (σ x)
       grind)
    | exact resolve eq5089 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5089
  have eq5092 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4902 eq5091
    | exact resolve eq5091 eq4902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4902 eq5091
  have eq5093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq5092
    | exact resolve eq5092 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5092
  have eq5094 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq5093
       have r₂ := eq27
       grind)
    | exact resolve eq5093 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5093
  have eq5137 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5094 eq1602
    | exact resolve eq1602 eq5094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602
  have eq5140 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq5137
    | exact resolve eq5137 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5137
  have eq5173 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5094 eq5140
    | exact resolve eq5140 eq5094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5094 eq5140
  have eq5207 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq5173
       grind)
    | exact superpose eq5173 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq5173
       grind)
    | exact resolve eq13 eq5173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5237 : ∀ X0 : G, x = (M.op (M.op x x) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 x x X0
       have i₂ := eq5173
       grind)
    | exact superpose eq5173 eq16
    | exact resolve eq16 eq5173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5247 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq5207 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5207
  have eq5257 : x = (M.op (M.op x x) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5237 x
       have i₂ := eq1332 (M.op x x) x
       grind)
    | exact superpose eq1332 eq5237
    | exact resolve eq5237 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5237
  have eq5289 : x = (M.op (M.op x x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5257
       have i₂ := eq1948 (M.op x x)
       grind)
    | exact superpose eq1948 eq5257
    | exact resolve eq5257 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5257
  have eq5303 : x = (M.op x (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5173 eq5289
    | exact resolve eq5289 eq5173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5173 eq5289
  have eq5307 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1625 eq5303
    | exact resolve eq5303 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5303
  have eq5319 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5307 eq1641
    | exact resolve eq1641 eq5307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641
  have eq6020 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5319 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq5319
       grind)
    | exact resolve eq13 eq5319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6062 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6020 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6020
  have eq6953 : (M.op x y) = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1348
       have i₂ := eq5247 sF0
       grind)
    | exact superpose eq5247 eq1348
    | exact resolve eq1348 eq5247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348 eq5247
  have eq7123 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5307 eq6953
    | exact resolve eq6953 eq5307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5307 eq6953
  have eq7357 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7123 eq42
    | exact resolve eq42 eq7123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq7123
  have eq7368 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq7357
    | exact resolve eq7357 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7357
  have eq7386 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7368 eq1056
    | (have j0 := eq1056 (σ (M.op x y))
       grind)
    | (have r₁ := eq1056 (σ (M.op x y))
       have r₂ := eq7368
       grind)
    | exact resolve eq1056 eq7368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7368
  have eq7390 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7386
  have eq7442 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7390 eq16
    | exact resolve eq16 eq7390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7464 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7442 x
       have i₂ := eq1332 (M.op sF1 sF1) x
       grind)
    | exact superpose eq1332 eq7442
    | exact resolve eq7442 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7442
  have eq7498 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7464
       have i₂ := eq1948 (M.op sF1 sF1)
       grind)
    | exact superpose eq1948 eq7464
    | exact resolve eq7464 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7464
  have eq7526 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7390 eq7498
    | exact resolve eq7498 eq7390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7390 eq7498
  have eq10775 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6062 eq5319
    | exact resolve eq5319 eq6062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5319 eq6062
  have eq10874 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq10775
  have eq11144 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10874 eq142
    | exact resolve eq142 eq10874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq10874
  have eq11160 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq11144
    | exact resolve eq11144 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq11144
  have eq11202 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1056 x
       have i₂ := eq11160
       grind)
    | exact superpose eq11160 eq1056
    | (have j0 := eq1056 x
       grind)
    | (have r₁ := eq1056 x
       have r₂ := eq11160
       grind)
    | exact resolve eq1056 eq11160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056 eq11160
  have eq11210 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq11202
  have eq11283 : ∀ X0 : G, x = (M.op (M.op x x) (M.op X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 x x X0
       have i₂ := eq11210
       grind)
    | exact superpose eq11210 eq16
    | exact resolve eq16 eq11210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11307 : x = (M.op (M.op x x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11283 x
       have i₂ := eq1332 (M.op x x) x
       grind)
    | exact superpose eq1332 eq11283
    | exact resolve eq11283 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332 eq11283
  have eq11344 : x = (M.op (M.op x x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11307
       have i₂ := eq1948 (M.op x x)
       grind)
    | exact superpose eq1948 eq11307
    | exact resolve eq11307 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948 eq11307
  have eq11363 : x = (M.op x (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11210 eq11344
    | exact resolve eq11344 eq11210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11210 eq11344
  have eq11375 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1625 eq11363
    | exact resolve eq11363 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625 eq11363
  have eq11376 : x = (M.op x y) := by grind
  clear eq11375
  have eq11382 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq11376
       grind)
    | exact superpose eq11376 eq22
    | exact resolve eq22 eq11376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq11376
  have eq11435 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11382 eq20
    | exact resolve eq20 eq11382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq11382
  have eq11496 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11435 eq7526
    | exact resolve eq7526 eq11435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7526
  have eq11500 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11496
    | exact resolve eq11496 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq11496
  have eq11501 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11500
  have eq11517 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq11501 eq27
    | exact resolve eq27 eq11501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq11501
  have eq11543 : False := by grind
  exact eq11543
