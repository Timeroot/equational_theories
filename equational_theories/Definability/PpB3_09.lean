import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pyx_Equation2373 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq64 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq9 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 (M.op X0 X1) x X1 X2
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op X0 (M.op X3 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq65 X2 x X0 X1
       have i₂ := eq65 X2 x X0 X3
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq700 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq693
    | (have j0 := eq693 X0 X1
       grind)
    | exact resolve eq693 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq1262 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X1 (M.op X0 X1)) (M.op X2 (M.op (M.op X3 (M.op X4 X3)) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq65 (M.op X3 (M.op X4 X3)) X4 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq66 X4 X1 X0 X3
       grind)
    | exact superpose eq66 eq65
    | exact resolve eq65 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq66
  have eq1723 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq700 x y
       grind)
    | exact superpose eq700 eq16
    | (have j1 := eq700 x y
       grind)
    | exact resolve eq16 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq2618 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 X1) (M.op X2 (M.op X0 X2)))) X3) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X3 (M.op X0 X1)
       have i₂ := eq163 (M.op X0 X1) X1 X0 X2
       grind)
    | (have i₁ := eq9 X1 X3 (M.op X0 X1)
       have i₂ := eq163 (M.op X0 X1) X2 X0 X1
       grind)
    | exact superpose eq163 eq9
    | exact resolve eq9 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq7496 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ (M.op X0 X0)) (M.op X2 (M.op (σ X0) X2)))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2618 (σ X0) (σ X0) X2 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq2618
    | exact resolve eq2618 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37763 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op (M.op X2 (M.op X1 X2)) (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1262 X1 X2 (σ (M.op X0 X0)) (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq64 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq64 eq1262
    | exact resolve eq1262 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq1262
  have eq71073 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1723
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1723
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq1723
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1723
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1723 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723
  have eq71074 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ x = y := by grind
  clear eq71073
  have eq115754 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op (σ (M.op X1 X1)) (σ X1)) (M.op X0 (σ X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq162 X2 (M.op X0 X2) (M.op (σ (M.op X1 X1)) (σ X1))
       have i₂ := eq37763 X1 X0 X2
       grind)
    | exact superpose eq37763 eq162
    | exact resolve eq162 eq37763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq37763
  have eq3766492 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op (σ (M.op y y)) (M.op X1 (M.op (σ y) X1)))) X0) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2618 (σ y) (σ x) X1 X0
       have i₂ := eq71074
       grind)
    | exact superpose eq71074 eq2618
    | exact resolve eq2618 eq71074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2618 eq71074
  have eq3767294 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3766492 x x
       have i₂ := eq7496 y x x
       grind)
    | exact superpose eq7496 eq3766492
    | exact resolve eq3766492 eq7496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7496 eq3766492
  have eq3767295 : (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3767294
  have eq3768537 : ∀ X0 : G, y = (M.op (M.op y x) (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (M.op y (σ X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq115754 y X0 y
       have i₂ := eq3767295
       grind)
    | exact superpose eq3767295 eq115754
    | exact resolve eq115754 eq3767295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3767295
  have eq3768541 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3768537 x
       have i₂ := eq115754 y x x
       grind)
    | exact superpose eq115754 eq3768537
    | exact resolve eq3768537 eq115754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115754 eq3768537
  have eq3768542 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3768541
  have eq3772285 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3768542
       grind)
    | exact superpose eq3768542 eq10
    | exact resolve eq10 eq3768542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3768542
  have eq3772621 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3772285
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3772285
    | exact resolve eq3772285 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3772285
  have eq3772622 : x = y := by grind
  clear eq3772621
  have eq3772624 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3772622
       grind)
    | exact superpose eq3772622 eq16
    | exact resolve eq16 eq3772622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3772622
  have eq3772625 : False := by grind
  exact eq3772625

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_y_pxy_Equation2373 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq9 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq29
    | (have j0 := eq29 X0 X1
       grind)
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq72 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op (M.op X2 (M.op X1 (σ X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) X2 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op X4 (M.op X3 X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X3 (M.op X1 X2) X2 X4
       have i₂ := eq24 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq221 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq38
    | (have j0 := eq38 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq38 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1897 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op X2 (M.op (M.op (M.op X0 (M.op (σ (M.op X1 X1)) (σ X1))) X0) (M.op X3 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X2 (σ (M.op X1 X1)) (σ X1) X3
       have i₂ := eq72 X1 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq72 eq25
    | exact resolve eq25 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq72
  have eq69849 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq221 x y
       grind)
    | exact superpose eq221 eq16
    | (have j1 := eq221 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq221 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq221 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq221 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq70049 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq69849
  have eq291542 : ∀ X0 X1 X2 : G, (σ y) = (M.op X0 (M.op (M.op (M.op X1 (M.op (σ (M.op x x)) (σ x))) X1) (M.op X2 (M.op X0 X2)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 X1 (σ x) (σ y) X0 X2
       have i₂ := eq70049
       grind)
    | exact superpose eq70049 eq112
    | exact resolve eq112 eq70049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70049
  have eq291921 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq291542 x x x
       have i₂ := eq1897 x x x x
       grind)
    | exact superpose eq1897 eq291542
    | exact resolve eq291542 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897 eq291542
  have eq291922 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq291921
  have eq295302 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op (M.op (M.op X1 (M.op (M.op x x) x)) X1) (M.op X2 (M.op X0 X2)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 X1 x y X0 X2
       have i₂ := eq291922
       grind)
    | exact superpose eq291922 eq112
    | exact resolve eq112 eq291922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291922
  have eq295675 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq295302 x x x
       have i₂ := eq112 x x x x x
       grind)
    | exact superpose eq112 eq295302
    | exact resolve eq295302 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq295302
  have eq295676 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq295675
  have eq317378 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq295676
       grind)
    | exact superpose eq295676 eq10
    | exact resolve eq10 eq295676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295676
  have eq317497 : x = y ∨ x = y := by
    first
    | (have i₁ := eq317378
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq317378
    | exact resolve eq317378 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317378
  have eq317498 : x = y := by grind
  clear eq317497
  have eq335639 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq317498
       grind)
    | exact superpose eq317498 eq16
    | exact resolve eq16 eq317498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317498
  have eq335640 : False := by grind
  exact eq335640

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_y_pxy_Equation2373 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
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
  clear eq52
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq84 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq83
    | exact resolve eq83 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq220 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 (M.op X1 X0)) (M.op (σ y) (M.op (σ x) (σ y))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op (M.op X4 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X0))) X3) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X1 X3 (M.op X4 (M.op X2 X4))
       have i₂ := eq55 X2 X0 X1 X4
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq611 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op X1 (M.op X2 X1)) (M.op X0 (σ x)))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq23034 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (M.op X1 X0)) (M.op (σ y) (M.op (σ x) (σ y))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq611 eq563
    | exact resolve eq563 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq611
  have eq134834 : y = (M.op x (M.op (M.op (σ x) (M.op x x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq23034 x y
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq23034
    | exact resolve eq23034 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq134841 : x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq23034 eq134834
    | exact resolve eq134834 eq23034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134834
  have eq134842 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq134841
  have eq135015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq134842 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq134842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134842
  have eq135022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq135015
    | exact resolve eq135015 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135015
  have eq135033 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq135022
       have r₂ := eq28
       grind)
    | exact resolve eq135022 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135022
  have eq135169 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq135033 eq23034
    | exact resolve eq23034 eq135033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23034 eq135033
  have eq135176 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq220 eq135169
    | exact resolve eq135169 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq135169
  have eq135177 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq135176
  have eq135399 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq135177 eq30
    | exact resolve eq30 eq135177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq135177
  have eq135624 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq135399
    | exact resolve eq135399 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq135399
  have eq135625 : x = y := by grind
  clear eq135624
  have eq135936 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq135625
       grind)
    | exact superpose eq135625 eq19
    | exact resolve eq19 eq135625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq135937 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq135625
       grind)
    | exact superpose eq135625 eq25
    | exact resolve eq25 eq135625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq135625
  have eq136159 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq135937
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq135937
    | exact resolve eq135937 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq135937
  have eq136189 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq136159 eq27
    | exact resolve eq27 eq136159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq136159
  have eq137522 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq136189 eq68
    | exact resolve eq68 eq136189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq136189
  have eq137791 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq137522
       have i₂ := eq135936
       grind)
    | exact superpose eq135936 eq137522
    | exact resolve eq137522 eq135936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135936 eq137522
  have eq137890 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq137791 eq15
    | exact resolve eq15 eq137791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137791
  have eq137970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq137890
    | exact resolve eq137890 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq137890
  have eq137991 : False := by grind
  exact eq137991

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_y_pyx_Equation2373 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
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
  clear eq52
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq37
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
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
  have eq102 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq220 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 (M.op X1 X0)) (M.op (σ y) (M.op (σ x) (σ y))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op (M.op X4 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X0))) X3) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X1 X3 (M.op X4 (M.op X2 X4))
       have i₂ := eq55 X2 X0 X1 X4
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq612 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op X1 (M.op X2 X1)) (M.op X0 (σ x)))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq22946 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (M.op X1 X0)) (M.op (σ y) (M.op (σ x) (σ y))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq612 eq564
    | exact resolve eq564 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq612
  have eq134880 : y = (M.op x (M.op (M.op (σ x) (M.op x x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq22946 x y
       have i₂ := eq102
       grind)
    | exact superpose eq102 eq22946
    | exact resolve eq22946 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq134887 : x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq22946 eq134880
    | exact resolve eq134880 eq22946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134880
  have eq134888 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq134887
  have eq135061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq134888 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq134888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134888
  have eq135068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq135061
    | exact resolve eq135061 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135061
  have eq135079 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq135068
       have r₂ := eq28
       grind)
    | exact resolve eq135068 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135068
  have eq135215 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq135079 eq22946
    | exact resolve eq22946 eq135079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22946 eq135079
  have eq135222 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq220 eq135215
    | exact resolve eq135215 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq135215
  have eq135223 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq135222
  have eq135445 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq135223 eq30
    | exact resolve eq30 eq135223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq135223
  have eq135670 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq135445
    | exact resolve eq135445 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq135445
  have eq135671 : x = y := by grind
  clear eq135670
  have eq135980 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq135671
       grind)
    | exact superpose eq135671 eq19
    | exact resolve eq19 eq135671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq135981 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq135671
       grind)
    | exact superpose eq135671 eq25
    | exact resolve eq25 eq135671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq135671
  have eq136203 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq135981
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq135981
    | exact resolve eq135981 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq135981
  have eq136233 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq136203 eq27
    | exact resolve eq27 eq136203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq136203
  have eq137564 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq136233 eq68
    | exact resolve eq68 eq136233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq136233
  have eq137833 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq137564
       have i₂ := eq135980
       grind)
    | exact superpose eq135980 eq137564
    | exact resolve eq137564 eq135980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135980 eq137564
  have eq137932 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq137833 eq15
    | exact resolve eq15 eq137833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137833
  have eq138012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq137932
    | exact resolve eq137932 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq137932
  have eq138033 : False := by grind
  exact eq138033

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation2452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq169 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq73 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq73 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq73 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq73 X1 X1
       grind)
    | exact resolve eq13 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq173 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq169 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq174 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq173 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq176 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq174
    | (have j0 := eq174 X0 X1
       grind)
    | exact resolve eq174 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq180 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq176 X0 X1
       have j1 := eq172 X0 X1
       grind)
    | (have r₁ := eq176 X0 X1
       have r₂ := eq172 X0 X1
       grind)
    | (have r₁ := eq176 X0 (k X1 X0)
       have r₂ := eq172 X0 X1
       grind)
    | (have r₁ := eq176 X0 X0
       have r₂ := eq172 X0 X0
       grind)
    | exact resolve eq176 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq176
  have eq536 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq180 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq180
    | exact resolve eq180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq180 x y
       grind)
    | exact superpose eq180 eq16
    | (have j1 := eq180 x y
       grind)
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq567 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq536 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq536
    | (have j0 := eq536 X0 X1
       grind)
    | exact resolve eq536 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq536
  have eq572 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq567 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq567
    | exact resolve eq567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq675 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq572 (τ X1) X0
       grind)
    | exact superpose eq572 eq18
    | (have j1 := eq572 (τ X1) X0
       grind)
    | exact resolve eq18 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq572
  have eq877 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq675 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq675
    | exact resolve eq675 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq934 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq877 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq877
    | (have j0 := eq877 X0 X1
       grind)
    | exact resolve eq877 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq996 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq550
       have i₂ := eq934 y x
       grind)
    | exact superpose eq934 eq550
    | (have j1 := eq934 (σ y) (σ x)
       grind)
    | (have r₁ := eq550
       have r₂ := eq934 y x
       grind)
    | exact resolve eq550 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq997 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq996
  have eq1043 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq997
  have eq1087 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq550
       have i₂ := eq1043
       grind)
    | exact superpose eq1043 eq550
    | exact resolve eq550 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq1043
  have eq1088 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1087
  have eq1089 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1088
  have eq1102 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1089
  have eq1111 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1102
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1102
    | exact resolve eq1102 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1162 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1111
       grind)
    | exact superpose eq1111 eq16
    | exact resolve eq16 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1234 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1162
       have i₂ := eq934 y x
       grind)
    | exact superpose eq934 eq1162
    | (have j1 := eq934 y x
       grind)
    | (have r₁ := eq1162
       have r₂ := eq934 y x
       grind)
    | exact resolve eq1162 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq1235 : y = (M.op x x) := by grind
  clear eq1234
  have eq1241 : (M.op x y) = (k y x) := by grind
  clear eq1235
  have eq1274 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1162
       have i₂ := eq1241
       grind)
    | exact superpose eq1241 eq1162
    | exact resolve eq1162 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq1241
  have eq1277 : False := by grind
  exact eq1277

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation2452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq62 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 x) x) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq62 X0
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq66 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq283 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq283 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq286 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq284 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq284 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq284 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq297 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq286 (σ X0)
       grind)
    | exact superpose eq286 eq15
    | exact resolve eq15 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq286 (τ X0)
       grind)
    | exact superpose eq286 eq31
    | exact resolve eq31 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq310 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq303 X0
       have i₂ := eq286 X0
       grind)
    | exact superpose eq286 eq303
    | exact resolve eq303 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq316 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq297 X0
       have i₂ := eq286 X0
       grind)
    | exact superpose eq286 eq297
    | exact resolve eq297 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq297
  have eq362 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq316 X0
       grind)
    | exact superpose eq316 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq316 X0
       grind)
    | exact superpose eq316 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq362 X0 X1
       have j1 := eq364 X0 X1
       grind)
    | (have r₁ := eq362 X0 X1
       have r₂ := eq364 X0 X1
       grind)
    | exact resolve eq362 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq503 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq366 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq366
    | exact resolve eq366 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) X2) = X2 ∨ (k X2 (k X0 (σ X1))) = (M.op (k X0 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq366 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq366
    | exact resolve eq366 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq366 X0 (σ X1)
       grind)
    | exact superpose eq366 eq15
    | (have j1 := eq366 X0 (σ X1)
       grind)
    | exact resolve eq15 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq543 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq503 (τ X0) X1
       grind)
    | exact superpose eq503 eq18
    | (have j1 := eq503 (τ X0) X1
       grind)
    | exact resolve eq18 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq741 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq543 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq543
    | exact resolve eq543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq791 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq741
    | (have j0 := eq741 X0 X1
       grind)
    | exact resolve eq741 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq1169 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq28
    | (have j1 := eq67 (σ X0)
       grind)
    | exact resolve eq28 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq67
  have eq1178 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X0 X0)))) ∨ (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1169 X0
       have i₂ := eq316 X0
       grind)
    | exact superpose eq316 eq1169
    | (have j0 := eq1169 X0
       grind)
    | exact resolve eq1169 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1188 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1178 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1178
    | (have j0 := eq1178 X0
       grind)
    | exact resolve eq1178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1196 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1188 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1188
    | (have j0 := eq1188 X0
       grind)
    | exact resolve eq1188 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1202 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1196 X0
       have i₂ := eq316 X0
       grind)
    | exact superpose eq316 eq1196
    | (have j0 := eq1196 X0
       grind)
    | exact resolve eq1196 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq1208 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1202 X0
       have i₂ := eq316 (M.op X0 X0)
       grind)
    | exact superpose eq316 eq1202
    | (have j0 := eq1202 X0
       grind)
    | exact resolve eq1202 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq1202
  have eq1227 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq514 x y
       grind)
    | exact superpose eq514 eq16
    | (have j1 := eq514 x y
       grind)
    | exact resolve eq16 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1251 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq514 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq1418 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1227
       have i₂ := eq791 x y
       grind)
    | exact superpose eq791 eq1227
    | (have j1 := eq791 (σ x) (σ y)
       grind)
    | (have r₁ := eq1227
       have r₂ := eq791 x y
       grind)
    | exact resolve eq1227 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1419 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1418
  have eq5949 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq364 (M.op X0 X0) X1
       have i₂ := eq1208 X0
       grind)
    | exact superpose eq1208 eq364
    | (have j0 := eq364 (M.op X0 X0) X1
       have j1 := eq1208 X0
       grind)
    | (have r₁ := eq364 (M.op X0 X0) X1
       have r₂ := eq1208 X0
       grind)
    | exact resolve eq364 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq1208
  have eq5992 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq5949 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5949
  have eq8402 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (M.op (σ (M.op (τ X0) (τ X0))) X1) = (k X1 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq5992 (τ X0) X1
       grind)
    | exact superpose eq5992 eq17
    | (have j1 := eq5992 (τ X0) X1
       grind)
    | exact resolve eq17 eq5992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq5992
  have eq8453 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (M.op (σ (M.op (τ X0) (τ X0))) X1) = (k X1 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8402 X0 X1
       have i₂ := eq310 X0
       grind)
    | exact superpose eq310 eq8402
    | (have j0 := eq8402 X0 X1
       grind)
    | exact resolve eq8402 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8402
  have eq8491 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (M.op (σ (M.op (τ X0) (τ X0))) X1) = (k X1 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8453 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq8453
    | (have j0 := eq8453 X0 X1
       grind)
    | exact resolve eq8453 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8453
  have eq8525 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op (σ (M.op (τ X0) (τ X0))) X1) = (k X1 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8491 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8491
    | (have j0 := eq8491 X0 X1
       grind)
    | exact resolve eq8491 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8491
  have eq8558 : ∀ X0 X1 : G, (M.op (σ (τ (M.op X0 X0))) X1) = (k X1 (σ (τ (M.op X0 X0)))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8525 X0 X1
       have i₂ := eq310 X0
       grind)
    | exact superpose eq310 eq8525
    | (have j0 := eq8525 X0 X1
       grind)
    | exact resolve eq8525 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310 eq8525
  have eq8585 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8558 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq8558
    | (have j0 := eq8558 X0 X1
       grind)
    | exact resolve eq8558 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8558
  have eq8675 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq8585 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8585
  have eq8683 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq8675 X0
       have j1 := eq503 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq8675 x
       have r₂ := eq503 (M.op x x) x
       grind)
    | exact resolve eq8675 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq8675
  have eq8722 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8683 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq8683
    | exact resolve eq8683 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq8683
  have eq18020 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (k X0 (k X1 (σ X2))) = X0 ∨ (k X0 (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (k X1 (σ X2))
       have i₂ := eq504 X1 X2 X0
       grind)
    | exact superpose eq504 eq13
    | (have j0 := eq13 X0 (k X1 (σ X2))
       have j1 := eq504 X1 X2 (k X1 (σ X2))
       grind)
    | (have r₁ := eq13 X2 (k X0 (σ X1))
       have r₂ := eq504 X0 X1 X2
       grind)
    | exact resolve eq13 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq18041 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (k X0 (k X1 (σ X2))) = X0 ∨ (k X0 (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq18020 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18020
  have eq18047 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) ∨ (k X0 (k X1 (σ X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq18041 X0 X1 X2
       have j1 := eq12 X0 (k X1 (σ X2))
       grind)
    | (have r₁ := eq18041 X0 X1 X2
       have r₂ := eq12 X0 (k X1 (σ X2))
       grind)
    | exact resolve eq18041 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18041
  have eq19698 : ∀ X0 X1 X2 : G, (M.op (k X1 (σ X2)) X0) ≠ X0 ∨ (k X0 (k X1 (σ X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq18047 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18047
  have eq19754 : ∀ X0 X1 X2 : G, (M.op (k X1 X0) X2) ≠ X2 ∨ (k X2 (k X1 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19698 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19698
    | exact resolve eq19698 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19698
  have eq19807 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19754 (M.op X0 X0) X0 x
       have i₂ := eq8722 X0
       grind)
    | exact superpose eq8722 eq19754
    | exact resolve eq19754 eq8722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8722 eq19754
  have eq19921 : y ≠ y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19807 x y
       have i₂ := eq1419
       grind)
    | exact superpose eq1419 eq19807
    | (have j0 := eq19807 x y
       grind)
    | (have r₁ := eq19807 x y
       have r₂ := eq1419
       grind)
    | (have r₁ := eq19807 (σ x) (σ y)
       have r₂ := eq1419
       grind)
    | exact resolve eq19807 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq19922 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19921
  have eq20288 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1251 x y
       have i₂ := eq19922
       grind)
    | exact superpose eq19922 eq1251
    | (have j0 := eq1251 x y
       grind)
    | exact resolve eq1251 eq19922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251 eq19922
  have eq20327 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20288
  have eq20328 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20327
  have eq20334 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20328
       grind)
    | exact superpose eq20328 eq16
    | exact resolve eq16 eq20328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20347 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq19807 (σ x) (σ y)
       have i₂ := eq20328
       grind)
    | exact superpose eq20328 eq19807
    | (have j0 := eq19807 (σ x) (σ y)
       grind)
    | (have r₁ := eq19807 (σ x) (σ y)
       have r₂ := eq20328
       grind)
    | exact resolve eq19807 eq20328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19807 eq20328
  have eq20349 : (σ y) = (k (σ y) (σ x)) := by grind
  clear eq20347
  have eq20351 : (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq20349
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq20349
    | exact resolve eq20349 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20349
  have eq20364 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq791 x y
       have i₂ := eq20351
       grind)
    | exact superpose eq20351 eq791
    | (have j0 := eq791 x y
       grind)
    | exact resolve eq791 eq20351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq20351
  have eq20455 : y = (M.op x y) := by
    first
    | (have r₁ := eq20364
       have r₂ := eq20334
       grind)
    | exact resolve eq20364 eq20334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20364
  have eq20515 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq20334
       have i₂ := eq20455
       grind)
    | exact superpose eq20455 eq20334
    | exact resolve eq20334 eq20455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20334 eq20455
  have eq20535 : False := by grind
  exact eq20535

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pyx_Equation2452 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq110 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 x) x) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq110 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq110
    | exact resolve eq110 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq279 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq286 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq279 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq279
    | (have j0 := eq279 X0 X1
       grind)
    | exact resolve eq279 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq703 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq286 x y
       grind)
    | exact superpose eq286 eq16
    | (have j1 := eq286 x y
       grind)
    | exact resolve eq16 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq4081 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq278 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq278
    | exact resolve eq278 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq4145 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4081 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4081
    | (have j0 := eq4081 X0 X1
       grind)
    | exact resolve eq4081 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4081
  have eq5650 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq703
       have i₂ := eq4145 x y
       grind)
    | exact superpose eq4145 eq703
    | (have j1 := eq4145 x y
       grind)
    | (have r₁ := eq703
       have r₂ := eq4145 x y
       grind)
    | (have r₁ := eq703
       have r₂ := eq4145 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq703
       have r₂ := eq4145 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq703 eq4145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703 eq4145
  have eq5651 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq5650
  have eq15169 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5651
       grind)
    | exact superpose eq5651 eq16
    | exact resolve eq16 eq5651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5651
  have eq15170 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq15169
       have r₂ := eq23 x
       grind)
    | exact resolve eq15169 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15169
  have eq15172 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15170
       grind)
    | exact superpose eq15170 eq10
    | exact resolve eq10 eq15170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15170
  have eq15231 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq15172
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15172
    | exact resolve eq15172 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15172
  have eq15233 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15231
       grind)
    | exact superpose eq15231 eq16
    | exact resolve eq16 eq15231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15231
  have eq15234 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq15233
       have r₂ := eq23 x
       grind)
    | exact resolve eq15233 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15233
  have eq15262 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq15234
       grind)
    | exact superpose eq15234 eq10
    | exact resolve eq10 eq15234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15234
  have eq15321 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15262
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15262
    | exact resolve eq15262 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15262
  have eq15322 : x = (M.op y y) := by grind
  clear eq15321
  have eq15331 : y = (M.op x y) := by
    first
    | (have i₁ := eq110 y
       have i₂ := eq15322
       grind)
    | exact superpose eq15322 eq110
    | exact resolve eq110 eq15322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq15332 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111 y
       have i₂ := eq15322
       grind)
    | exact superpose eq15322 eq111
    | exact resolve eq111 eq15322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq15322
  have eq15453 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15332
       grind)
    | exact superpose eq15332 eq16
    | exact resolve eq16 eq15332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15332
  have eq15465 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq15453
       have i₂ := eq15331
       grind)
    | exact superpose eq15331 eq15453
    | exact resolve eq15453 eq15331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15331 eq15453
  have eq15466 : False := by grind
  exact eq15466

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation2452 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq180 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq182 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq622 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq180 x y
       grind)
    | exact superpose eq180 eq16
    | (have j1 := eq180 x y
       grind)
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq5544 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq182
    | exact resolve eq182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq5653 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5544 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5544
    | (have j0 := eq5544 X0 X1
       grind)
    | exact resolve eq5544 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5544
  have eq5829 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq627 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq627
    | (have j0 := eq627 (τ X1) (τ X0)
       grind)
    | exact resolve eq627 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq5849 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5829 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5829
    | (have j0 := eq5829 X0 X1
       grind)
    | exact resolve eq5829 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5829
  have eq5862 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5849 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5849
    | (have j0 := eq5849 X0 X1
       grind)
    | exact resolve eq5849 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5849
  have eq5871 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5862 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5862
    | (have j0 := eq5862 X0 X1
       grind)
    | exact resolve eq5862 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5862
  have eq5878 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5871 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5871
    | (have j0 := eq5871 X0 X1
       grind)
    | exact resolve eq5871 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5871
  have eq5880 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5878 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5878
    | (have j0 := eq5878 X0 X1
       grind)
    | exact resolve eq5878 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5878
  have eq5882 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5880 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5880
    | (have j0 := eq5880 X0 X1
       grind)
    | exact resolve eq5880 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5880
  have eq15189 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq622
       have i₂ := eq5653 y x
       grind)
    | exact superpose eq5653 eq622
    | (have j1 := eq5653 (σ y) (σ x)
       grind)
    | (have r₁ := eq622
       have r₂ := eq5653 y x
       grind)
    | (have r₁ := eq622
       have r₂ := eq5653 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq622
       have r₂ := eq5653 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq622 eq5653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq5653
  have eq15190 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15189
  have eq24023 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15190
       grind)
    | exact superpose eq15190 eq16
    | exact resolve eq16 eq15190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15190
  have eq24024 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq24023
       have r₂ := eq22 x
       grind)
    | exact resolve eq24023 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24023
  have eq24029 : x ≠ x ∨ x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq24024
       grind)
    | exact superpose eq24024 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq24024
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq24024
       grind)
    | exact resolve eq13 eq24024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24024
  have eq24031 : x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24029
  have eq26023 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24031
       grind)
    | exact superpose eq24031 eq16
    | exact resolve eq16 eq24031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24031
  have eq26024 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq26023
       have r₂ := eq22 x
       grind)
    | exact resolve eq26023 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26023
  have eq26029 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq26024
       grind)
    | exact superpose eq26024 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq26024
       grind)
    | exact resolve eq13 eq26024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26024
  have eq26034 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by grind
  clear eq26029
  have eq26035 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by grind
  clear eq26034
  have eq26039 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq26035
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq26035
    | exact resolve eq26035 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26035
  have eq26281 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq627 x y
       have i₂ := eq26039
       grind)
    | exact superpose eq26039 eq627
    | (have j0 := eq627 x y
       grind)
    | (have r₁ := eq627 x y
       have r₂ := eq26039
       grind)
    | exact resolve eq627 eq26039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26039
  have eq26298 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq26281
  have eq26299 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq26298
  have eq26304 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq627 x y
       grind)
    | (have r₁ := eq26299
       have r₂ := eq627 x y
       grind)
    | exact resolve eq26299 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627 eq26299
  have eq26308 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26304
       grind)
    | exact superpose eq26304 eq16
    | exact resolve eq16 eq26304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26312 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq26304
       grind)
    | exact superpose eq26304 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq26304
       grind)
    | exact resolve eq13 eq26304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26304
  have eq26317 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq26312
  have eq26318 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq26317
  have eq26322 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq26318
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq26318
    | exact resolve eq26318 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26318
  have eq26332 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq26322
       grind)
    | exact superpose eq26322 eq10
    | exact resolve eq10 eq26322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26322
  have eq26400 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq26332
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26332
    | exact resolve eq26332 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26332
  have eq26402 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26400
       grind)
    | exact superpose eq26400 eq16
    | exact resolve eq16 eq26400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26400
  have eq26403 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq26402
       have r₂ := eq22 x
       grind)
    | exact resolve eq26402 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26402
  have eq26414 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq26403
       grind)
    | exact superpose eq26403 eq10
    | exact resolve eq10 eq26403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26403
  have eq26483 : x = (k y x) := by
    first
    | (have i₁ := eq26414
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26414
    | exact resolve eq26414 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26414
  have eq26498 : x ≠ x ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5882 y x
       have i₂ := eq26483
       grind)
    | exact superpose eq26483 eq5882
    | (have j0 := eq5882 y x
       grind)
    | (have r₁ := eq5882 y x
       have r₂ := eq26483
       grind)
    | exact resolve eq5882 eq26483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5882 eq26483
  have eq26507 : x = (M.op x y) ∨ x = y := by grind
  clear eq26498
  have eq26511 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq26308
       have i₂ := eq26507
       grind)
    | exact superpose eq26507 eq26308
    | exact resolve eq26308 eq26507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26308 eq26507
  have eq26522 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq26511
  have eq26525 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26522
       grind)
    | exact superpose eq26522 eq16
    | exact resolve eq16 eq26522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26522
  have eq26530 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq26525
       have r₂ := eq22 x
       grind)
    | exact resolve eq26525 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26525
  have eq26531 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26530
       grind)
    | exact superpose eq26530 eq16
    | exact resolve eq16 eq26530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26532 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq26530
       grind)
    | exact superpose eq26530 eq10
    | exact resolve eq10 eq26530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26530
  have eq26600 : x = y := by
    first
    | (have i₁ := eq26532
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26532
    | exact resolve eq26532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26532
  have eq26601 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq26531
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq26531
    | exact resolve eq26531 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26531
  have eq26602 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq26601
       have i₂ := eq26600
       grind)
    | exact superpose eq26600 eq26601
    | exact resolve eq26601 eq26600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26600 eq26601
  have eq26603 : False := by grind
  exact eq26603
