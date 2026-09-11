import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3873`: `x ◇ x = (x ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pyx_pxx_pyx_Equation3873 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3873 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3873.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X3)) (M.op (M.op X0 X1) (M.op X2 X3))) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X2 X3)) X0 X1
       have i₂ := eq9 (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq88 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 (σ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq9
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq540 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq540
    | (have j0 := eq540 (σ X0) (σ X1)
       grind)
    | exact resolve eq540 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq540 X1 (σ X0)
       grind)
    | exact superpose eq540 eq22
    | (have j1 := eq540 X1 (σ X0)
       grind)
    | exact resolve eq22 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1172 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq541 X1 X0
       have i₂ := eq540 X1 X0
       grind)
    | exact superpose eq540 eq541
    | (have j0 := eq541 X1 X0
       have j1 := eq540 (σ X1) (σ X0)
       grind)
    | exact resolve eq541 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3295 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X2 X3))) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X2 X3))) (M.op (M.op X0 X1) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X2 X3)) (M.op X0 X1) (M.op X2 X3)
       have i₂ := eq62 X0 X1 X2 X3
       grind)
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1) (M.op X2 X3)
       have i₂ := eq62 X0 X1 X2 X3
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq8038 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1172 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1172
    | (have j0 := eq1172 X0 (σ X1)
       grind)
    | exact resolve eq1172 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8062 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1172 x y
       grind)
    | exact superpose eq1172 eq16
    | (have j1 := eq1172 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1172 x y
       grind)
    | exact resolve eq16 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq8110 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq8062
  have eq8155 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq547 y (σ x)
       have i₂ := eq8110
       grind)
    | exact superpose eq8110 eq547
    | (have j0 := eq547 y (σ x)
       grind)
    | exact resolve eq547 eq8110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq8160 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ x)) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq8110
       grind)
    | exact superpose eq8110 eq9
    | exact resolve eq9 eq8110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8165 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq8155
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8155
    | exact resolve eq8155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8155
  have eq8309 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq8160 (σ y)
       have i₂ := eq8110
       grind)
    | exact superpose eq8110 eq8160
    | exact resolve eq8160 eq8110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8160
  have eq8339 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq8309
  have eq8363 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq8339
       have i₂ := eq77 y
       grind)
    | exact superpose eq77 eq8339
    | exact resolve eq8339 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8339
  have eq8480 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8363
       grind)
    | exact superpose eq8363 eq16
    | exact resolve eq16 eq8363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8484 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq89 x (σ y)
       have i₂ := eq8363
       grind)
    | exact superpose eq8363 eq89
    | exact resolve eq89 eq8363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq8363
  have eq8497 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq8484
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8484
    | exact resolve eq8484 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8484
  have eq8500 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq540 eq8497
    | (have j1 := eq540 y x
       grind)
    | exact resolve eq8497 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8497
  have eq8503 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq8500
       have r₂ := eq8480
       grind)
    | exact resolve eq8500 eq8480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8500
  have eq8539 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ y)) X0) ∨ x = (k x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq8165
       grind)
    | exact superpose eq8165 eq9
    | exact resolve eq9 eq8165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9272 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ x = (M.op y x) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq8539 (σ x)
       have i₂ := eq8165
       grind)
    | exact superpose eq8165 eq8539
    | exact resolve eq8539 eq8165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8165 eq8539
  have eq9308 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ x = (M.op y x) := by grind
  clear eq9272
  have eq9337 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq9308
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq9308
    | exact resolve eq9308 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9308
  have eq9386 : (σ x) = (σ (M.op x x)) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq8110 eq9337
    | exact resolve eq9337 eq8110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9337
  have eq9504 : (τ (σ x)) = (M.op x x) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq9386
       grind)
    | exact superpose eq9386 eq10
    | exact resolve eq10 eq9386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9386
  have eq9657 : x = (k x y) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq9504
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9504
    | exact resolve eq9504 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9504
  have eq9663 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq540 x y
       have i₂ := eq9657
       grind)
    | exact superpose eq9657 eq540
    | (have j0 := eq540 y x
       grind)
    | exact resolve eq540 eq9657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9664 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq9663
  have eq9670 : y ≠ y ∨ (M.op y x) = (M.op y y) ∨ (k x y) = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq9664
       grind)
    | exact superpose eq9664 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq9664
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq9664
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq9664
       grind)
    | exact resolve eq13 eq9664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9672 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 y) X0) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq9664
       grind)
    | exact superpose eq9664 eq9
    | exact resolve eq9 eq9664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9673 : (M.op y x) = (M.op y y) ∨ (k x y) = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq9670
  have eq9677 : (M.op y x) = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq9657 eq9673
    | exact resolve eq9673 eq9657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9657 eq9673
  have eq9678 : (M.op y x) = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq9677
  have eq9746 : (M.op y x) = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9672 x
       have i₂ := eq9664
       grind)
    | exact superpose eq9664 eq9672
    | exact resolve eq9672 eq9664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9664 eq9672
  have eq9784 : (M.op y x) = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq9746
  have eq9927 : (M.op y y) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq9784 eq9678
    | exact resolve eq9678 eq9784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9678 eq9784
  have eq9936 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq8503
       have i₂ := eq9927
       grind)
    | exact superpose eq9927 eq8503
    | exact resolve eq8503 eq9927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9927
  have eq9972 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq9936
  have eq9973 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq9972
  have eq9981 : (σ x) ≠ (σ (M.op y y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq9973 eq8503
    | exact resolve eq8503 eq9973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8503
  have eq9984 : x ≠ x ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq9973
       grind)
    | exact superpose eq9973 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq9973
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq9973
       grind)
    | exact resolve eq13 eq9973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9985 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 x) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq9973
       grind)
    | exact superpose eq9973 eq9
    | exact resolve eq9 eq9973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9986 : (M.op x y) = (M.op x x) ∨ (M.op y y) = (k y x) ∨ x = (M.op x x) := by grind
  clear eq9984
  have eq10015 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9985 y
       have i₂ := eq9973
       grind)
    | exact superpose eq9973 eq9985
    | exact resolve eq9985 eq9973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9973 eq9985
  have eq10048 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq10015
  have eq11101 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq10048 eq9986
    | exact resolve eq9986 eq10048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9986
  have eq11102 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq11101
       have r₂ := eq12 y x
       grind)
    | exact resolve eq11101 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11101
  have eq11104 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq541 y x
       have i₂ := eq11102
       grind)
    | exact superpose eq11102 eq541
    | (have j0 := eq541 y x
       grind)
    | exact resolve eq541 eq11102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11102
  have eq11105 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq11104
       have r₂ := eq16
       grind)
    | exact resolve eq11104 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11104
  have eq11118 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ x)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq11105
       grind)
    | exact superpose eq11105 eq9
    | exact resolve eq9 eq11105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11164 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11118 (σ y)
       have i₂ := eq11105
       grind)
    | exact superpose eq11105 eq11118
    | exact resolve eq11118 eq11105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11105 eq11118
  have eq11207 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq11164
  have eq11240 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11207
       have i₂ := eq77 y
       grind)
    | exact superpose eq77 eq11207
    | exact resolve eq11207 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11207
  have eq11291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq10048 eq11240
    | exact resolve eq11240 eq10048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10048 eq11240
  have eq11308 : x = (M.op x x) := by
    first
    | (have r₁ := eq11291
       have r₂ := eq16
       grind)
    | exact resolve eq11291 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11291
  have eq11379 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq11308
       grind)
    | exact superpose eq11308 eq12
    | (have j0 := eq12 X0 x
       grind)
    | exact resolve eq12 eq11308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11380 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq88 x X0
       have i₂ := eq11308
       grind)
    | exact superpose eq11308 eq88
    | exact resolve eq88 eq11308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq11406 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 x) X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq11308
       grind)
    | exact superpose eq11308 eq9
    | exact resolve eq9 eq11308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29708 : ∀ X0 X1 : G, (M.op (M.op x x) (M.op x (M.op X0 X1))) = (M.op (M.op (M.op x x) (M.op x (M.op X0 X1))) (M.op x (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3295 x x x x
       have i₂ := eq11308
       grind)
    | exact superpose eq11308 eq3295
    | exact resolve eq3295 eq11308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3295
  have eq29879 : ∀ X0 X1 : G, (M.op x (M.op x (M.op X0 X1))) = (M.op (M.op x (M.op x (M.op X0 X1))) (M.op x (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29708 X0 X1
       have i₂ := eq11308
       grind)
    | exact superpose eq11308 eq29708
    | exact resolve eq29708 eq11308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29708
  have eq940766 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq8038 X0 X1
       grind)
    | exact superpose eq8038 eq10
    | (have j1 := eq8038 X0 X1
       grind)
    | exact resolve eq10 eq8038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8038
  have eq1077988 : (τ (σ x)) = (M.op (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ y)) = (M.op x (τ (σ y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq940766 (σ y) x
       have i₂ := eq8110
       grind)
    | exact superpose eq8110 eq940766
    | (have j0 := eq940766 (σ y) x
       grind)
    | exact resolve eq940766 eq8110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940766
  have eq1078145 : (M.op y x) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ y)) = (M.op x (τ (σ y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1077988
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1077988
    | exact resolve eq1077988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077988
  have eq1078622 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ y)) = (M.op x (τ (σ y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1078145
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1078145
    | exact resolve eq1078145 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078145
  have eq1078623 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ y)) = (M.op x (τ (σ y))) := by grind
  clear eq1078622
  have eq1079093 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1078623
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1078623
    | exact resolve eq1078623 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078623
  have eq1079114 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1079093
       grind)
    | exact superpose eq1079093 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1079093
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1079093
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1079093
       grind)
    | exact resolve eq13 eq1079093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079093
  have eq1079162 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq1079114
  have eq1079177 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1079162
       have i₂ := eq77 y
       grind)
    | exact superpose eq77 eq1079162
    | exact resolve eq1079162 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079162
  have eq1079187 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1079177
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq1079177
    | exact resolve eq1079177 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079177
  have eq1079194 : (σ x) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1079187
       have i₂ := eq11308
       grind)
    | exact superpose eq11308 eq1079187
    | exact resolve eq1079187 eq11308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079187
  have eq1079198 : (σ x) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1079194
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1079194
    | exact resolve eq1079194 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079194
  have eq1079201 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8110 eq1079198
    | exact resolve eq1079198 eq8110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8110 eq1079198
  have eq1079203 : (σ x) = (σ (k x y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1079201
       have r₂ := eq9981
       grind)
    | exact resolve eq1079201 eq9981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9981 eq1079201
  have eq1079204 : (σ x) = (σ (M.op y x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq540 eq1079203
    | (have j1 := eq540 y x
       grind)
    | exact resolve eq1079203 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq1079203
  have eq1079655 : (M.op y x) = (τ (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y x)
       have i₂ := eq1079204
       grind)
    | exact superpose eq1079204 eq10
    | exact resolve eq10 eq1079204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079204
  have eq1079824 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1079655
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1079655
    | exact resolve eq1079655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079655
  have eq1079825 : y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq1079824
  have eq1079828 : (σ y) ≠ (σ (M.op y y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1079825 eq8480
    | exact resolve eq8480 eq1079825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8480
  have eq1079856 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq29879 x y
       have i₂ := eq1079825
       grind)
    | exact superpose eq1079825 eq29879
    | exact resolve eq29879 eq1079825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29879
  have eq1079912 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1079825 eq1079856
    | exact resolve eq1079856 eq1079825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079856
  have eq1079946 : y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1079825 eq1079912
    | exact resolve eq1079912 eq1079825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079825 eq1079912
  have eq1080217 : (σ y) ≠ (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1079946 eq1079828
    | exact resolve eq1079828 eq1079946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079828 eq1079946
  have eq1080218 : x = (M.op y x) := by grind
  clear eq1080217
  have eq1080219 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11406 y
       have i₂ := eq1080218
       grind)
    | exact superpose eq1080218 eq11406
    | exact resolve eq11406 eq1080218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11406
  have eq1080221 : x ≠ x ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1080218
       grind)
    | exact superpose eq1080218 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1080218
       grind)
    | exact resolve eq13 eq1080218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080218
  have eq1080269 : (M.op x y) = (M.op x x) ∨ (M.op y y) = (k y x) := by grind
  clear eq1080221
  have eq1080306 : x = (M.op x y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq1080269
       have i₂ := eq11308
       grind)
    | exact superpose eq11308 eq1080269
    | exact resolve eq1080269 eq11308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11308 eq1080269
  have eq1080500 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1080306
       have i₂ := eq1080219
       grind)
    | exact superpose eq1080219 eq1080306
    | exact resolve eq1080306 eq1080219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080306
  have eq1080501 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq11379 y
       grind)
    | (have r₁ := eq1080500
       have r₂ := eq11379 y
       grind)
    | exact resolve eq1080500 eq11379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11379 eq1080500
  have eq1080503 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq541 y x
       have i₂ := eq1080501
       grind)
    | exact superpose eq1080501 eq541
    | (have j0 := eq541 y x
       grind)
    | exact resolve eq541 eq1080501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq1080501
  have eq1080504 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1080503
       have r₂ := eq16
       grind)
    | exact resolve eq1080503 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080503
  have eq1080515 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11380 (σ y)
       have i₂ := eq1080504
       grind)
    | exact superpose eq1080504 eq11380
    | exact resolve eq11380 eq1080504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11380 eq1080504
  have eq1080580 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1080515
       have i₂ := eq77 y
       grind)
    | exact superpose eq77 eq1080515
    | exact resolve eq1080515 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1080515
  have eq1080600 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1080580
       have i₂ := eq1080219
       grind)
    | exact superpose eq1080219 eq1080580
    | exact resolve eq1080580 eq1080219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080219 eq1080580
  have eq1080608 : False := by grind
  exact eq1080608

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq52 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq167 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq174 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq167 X0 X1
       have j1 := eq52 X0 X1
       grind)
    | (have r₁ := eq167 X0 X1
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq167 X0 X0
       have r₂ := eq52 X0 X0
       grind)
    | exact resolve eq167 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq167
  have eq400 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq174 (σ X1) (σ X0)
       grind)
    | exact superpose eq174 eq15
    | exact resolve eq15 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq400 X0 X1
       have i₂ := eq174 X1 X0
       grind)
    | exact superpose eq174 eq400
    | exact resolve eq400 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq400
  have eq410 : False := by grind
  exact eq410

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_y_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq264 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq265 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq264 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq264
    | (have j0 := eq264 (σ X0) (σ X1)
       grind)
    | exact resolve eq264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq264 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq264
    | (have j0 := eq264 (τ X0) (τ X1)
       grind)
    | exact resolve eq264 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq357 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq265 X1 X0
       have i₂ := eq264 X1 X0
       grind)
    | exact superpose eq264 eq265
    | (have j0 := eq265 X1 X0
       have j1 := eq264 (σ X1) (σ X0)
       grind)
    | exact resolve eq265 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq539 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq266 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq546 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq539 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq539
    | (have j0 := eq539 (σ X1) (σ X0)
       grind)
    | exact resolve eq539 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq556 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq546
    | (have j0 := eq546 X0 X1
       grind)
    | exact resolve eq546 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq558 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq556 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq556
    | (have j0 := eq556 X0 X1
       grind)
    | exact resolve eq556 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq559 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq558
    | (have j0 := eq558 X0 X1
       grind)
    | exact resolve eq558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq560 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq559
    | (have j0 := eq559 X0 X1
       grind)
    | exact resolve eq559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq562 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq560 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq560
    | (have j0 := eq560 (σ X0) (σ X1)
       grind)
    | exact resolve eq560 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq4612 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq357 x y
       grind)
    | exact superpose eq357 eq16
    | (have j1 := eq357 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq357 x y
       grind)
    | exact resolve eq16 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq4625 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4612
  have eq4641 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4625
       grind)
    | exact superpose eq4625 eq16
    | exact resolve eq16 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4643 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq4625
       grind)
    | exact superpose eq4625 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq4625
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4625
       grind)
    | exact resolve eq13 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4644 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq4625
       grind)
    | exact superpose eq4625 eq12
    | exact resolve eq12 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4625
  have eq4646 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4643
  have eq4648 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4644
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4644
    | exact resolve eq4644 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644
  have eq4649 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4646
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4646
    | exact resolve eq4646 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4646
  have eq4651 : (σ (M.op x y)) = (σ x) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264 eq4648
    | (have j1 := eq264 y x
       grind)
    | exact resolve eq4648 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4648
  have eq4652 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264 eq4649
    | (have j1 := eq264 y x
       grind)
    | exact resolve eq4649 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq4649
  have eq4654 : x = (M.op x y) := by grind
  clear eq4641 eq4651 eq4652
  have eq4656 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4654
       grind)
    | exact superpose eq4654 eq16
    | exact resolve eq16 eq4654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4658 : x ≠ x ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq4654
       grind)
    | exact superpose eq4654 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4654
       grind)
    | exact resolve eq13 eq4654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4659 : x ≠ y ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq4654
       grind)
    | exact superpose eq4654 eq12
    | exact resolve eq12 eq4654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654
  have eq4661 : x = y ∨ x = (k y x) := by grind
  clear eq4658
  have eq4662 : x = (k y x) := by
    first
    | (have r₁ := eq4661
       have r₂ := eq4659
       grind)
    | exact resolve eq4661 eq4659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4659 eq4661
  have eq4669 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq562 y x
       have i₂ := eq4662
       grind)
    | exact superpose eq4662 eq562
    | (have j0 := eq562 y x
       grind)
    | exact resolve eq562 eq4662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq4662
  have eq4672 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4669
  have eq4679 : False := by grind
  exact eq4679

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq264 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq265 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3473 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq264 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq264
    | (have j0 := eq264 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq264 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5377 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ X1) = (k (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq265 X0 X1
       grind)
    | exact superpose eq265 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq265 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq265 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (τ X1)
       have r₂ := eq265 X1 X1
       grind)
    | exact resolve eq13 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5379 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) (τ X1)
       have i₂ := eq265 X0 X1
       grind)
    | exact superpose eq265 eq12
    | (have j0 := eq12 (τ X0) (τ X1)
       have j1 := eq265 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq265 X0 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X1)
       have r₂ := eq265 X0 X1
       grind)
    | exact resolve eq12 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq5384 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5379 X0 X1
       have j1 := eq12 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq5379 X0 X0
       have r₂ := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq5379 X0 X1
       have r₂ := eq12 (τ X0) (τ X1)
       grind)
    | exact resolve eq5379 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5379
  have eq5385 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ X1) = (k (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5377 X0 X1
       have j1 := eq13 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq5377 X0 X1
       have r₂ := eq13 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq5377 X1 X1
       have r₂ := eq13 (τ X1) (τ X1)
       grind)
    | exact resolve eq5377 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5377
  have eq5390 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5384 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq5384
    | (have j0 := eq5384 X0 X1
       grind)
    | exact resolve eq5384 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5384
  have eq5391 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5385 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq5385
    | (have j0 := eq5385 X0 X1
       grind)
    | exact resolve eq5385 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5385
  have eq5392 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5391 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5391
  have eq5394 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5390 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5390
    | (have j0 := eq5390 (σ X0) (σ X1)
       grind)
    | exact resolve eq5390 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5390
  have eq5452 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5394 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5394
    | (have j0 := eq5394 X0 X1
       grind)
    | exact resolve eq5394 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5394
  have eq5475 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5452 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5452
    | (have j0 := eq5452 X0 X1
       grind)
    | exact resolve eq5452 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5452
  have eq5496 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5475 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5475
    | (have j0 := eq5475 X0 X1
       grind)
    | exact resolve eq5475 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5475
  have eq5517 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5496 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5496
    | (have j0 := eq5496 X0 X1
       grind)
    | exact resolve eq5496 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5496
  have eq5526 : ∀ X0 X1 : G, (M.op (τ (σ X1)) X0) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5517 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5517
    | (have j0 := eq5517 X0 X1
       grind)
    | exact resolve eq5517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5517
  have eq5535 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5526 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5526
    | (have j0 := eq5526 X0 X1
       grind)
    | exact resolve eq5526 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5526
  have eq5553 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5535 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5535
    | (have j0 := eq5535 (σ X0) (σ X1)
       grind)
    | exact resolve eq5535 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5535
  have eq5577 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5392 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5392
    | (have j0 := eq5392 (σ X0) (σ X1)
       grind)
    | exact resolve eq5392 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5392
  have eq5635 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5577 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5577
    | (have j0 := eq5577 X0 X1
       grind)
    | exact resolve eq5577 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5577
  have eq5658 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5635 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5635
    | (have j0 := eq5635 X0 X1
       grind)
    | exact resolve eq5635 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5635
  have eq5679 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (k X0 X1) ≠ X0 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5658 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5658
    | (have j0 := eq5658 X0 X1
       grind)
    | exact resolve eq5658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5658
  have eq5700 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5679 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5679
    | (have j0 := eq5679 X0 X1
       grind)
    | exact resolve eq5679 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5679
  have eq5709 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5700 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5700
    | (have j0 := eq5700 X0 X1
       grind)
    | exact resolve eq5700 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5700
  have eq5718 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5709 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5709
    | (have j0 := eq5709 X0 X1
       grind)
    | exact resolve eq5709 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5709
  have eq5736 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5718 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5718
    | (have j0 := eq5718 (σ X0) (σ X1)
       grind)
    | exact resolve eq5718 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5718
  have eq229849 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3473 x y
       grind)
    | exact superpose eq3473 eq16
    | (have j1 := eq3473 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3473 x y
       grind)
    | exact resolve eq16 eq3473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3473
  have eq229881 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq229849
  have eq229901 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq229881
       grind)
    | exact superpose eq229881 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq229881
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq229881
       grind)
    | exact resolve eq13 eq229881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229908 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq229881
  have eq229909 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq229901
  have eq229911 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq229909
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq229909
    | exact resolve eq229909 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229909
  have eq229913 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14 eq229911
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq229911 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229911
  have eq229915 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq229913
       have r₂ := eq229908
       grind)
    | exact resolve eq229913 eq229908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229908 eq229913
  have eq229922 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq229915
       grind)
    | exact superpose eq229915 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq229915
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq229915
       grind)
    | exact resolve eq12 eq229915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229915
  have eq229929 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq229922
  have eq229932 : (σ y) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq229929
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq229929
    | exact resolve eq229929 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229929
  have eq229933 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14 eq229932
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq229932 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229932
  have eq229934 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq229933
       grind)
    | exact superpose eq229933 eq10
    | exact resolve eq10 eq229933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229933
  have eq230082 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq229934
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq229934
    | exact resolve eq229934 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229934
  have eq230083 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq230082
  have eq230087 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq230083
       grind)
    | exact superpose eq230083 eq10
    | exact resolve eq10 eq230083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230083
  have eq230234 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq230087
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq230087
    | exact resolve eq230087 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230087
  have eq230235 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq230234
  have eq230241 : x ≠ y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq230235
       grind)
    | exact superpose eq230235 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq230235
       grind)
    | exact resolve eq12 eq230235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230242 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq230235
       grind)
    | exact superpose eq230235 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq230235
       grind)
    | exact resolve eq13 eq230235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230249 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq230250 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq230242
  have eq230251 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq230250
       have r₂ := eq230249
       grind)
    | exact resolve eq230250 eq230249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230249 eq230250
  have eq230252 : x ≠ y ∨ y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq230241
       have r₂ := eq12 y x
       grind)
    | exact resolve eq230241 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230241
  have eq230284 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5553 y x
       have i₂ := eq230251
       grind)
    | exact superpose eq230251 eq5553
    | (have j0 := eq5553 y x
       grind)
    | exact resolve eq5553 eq230251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5553 eq230251
  have eq230295 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq230284
  have eq230315 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq230295
       grind)
    | exact superpose eq230295 eq16
    | exact resolve eq16 eq230295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230295
  have eq230330 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq230235 eq230315
    | exact resolve eq230315 eq230235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230315
  have eq230331 : x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq230330
  have eq230334 : x ≠ x ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq230331
       grind)
    | exact superpose eq230331 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq230331
       grind)
    | exact resolve eq12 eq230331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230342 : y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq230334
  have eq230353 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5736 y x
       have i₂ := eq230342
       grind)
    | exact superpose eq230342 eq5736
    | (have j0 := eq5736 y x
       grind)
    | exact resolve eq5736 eq230342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5736 eq230342
  have eq230362 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq230353
  have eq230363 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq230362
  have eq230374 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq230363
       grind)
    | exact superpose eq230363 eq16
    | exact resolve eq16 eq230363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230363
  have eq230386 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq230331 eq230374
    | exact resolve eq230374 eq230331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230331 eq230374
  have eq230387 : (σ x) = (σ y) := by grind
  clear eq230386
  have eq230388 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq230387
       grind)
    | exact superpose eq230387 eq16
    | exact resolve eq16 eq230387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230389 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq230387
       grind)
    | exact superpose eq230387 eq10
    | exact resolve eq10 eq230387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230387
  have eq230536 : x = y := by
    first
    | (have i₁ := eq230389
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq230389
    | exact resolve eq230389 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230389
  have eq230537 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq230235
       have i₂ := eq230536
       grind)
    | exact superpose eq230536 eq230235
    | exact resolve eq230235 eq230536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230235
  have eq230541 : x ≠ x ∨ y = (k y x) := by
    first
    | (have i₁ := eq230252
       have i₂ := eq230536
       grind)
    | exact superpose eq230536 eq230252
    | (have r₁ := eq230252
       have r₂ := eq230536
       grind)
    | exact resolve eq230252 eq230536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230252
  have eq230542 : y = (k y x) := by grind
  clear eq230541
  have eq230543 : x = (k x x) := by
    first
    | (have i₁ := eq230542
       have i₂ := eq230536
       grind)
    | exact superpose eq230536 eq230542
    | exact resolve eq230542 eq230536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230542
  have eq230547 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq230537
       have i₂ := eq230536
       grind)
    | exact superpose eq230536 eq230537
    | exact resolve eq230537 eq230536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230537
  have eq230548 : x = (M.op x x) := by grind
  clear eq230547
  have eq230579 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq264 x x
       have i₂ := eq230543
       grind)
    | exact superpose eq230543 eq264
    | (have j0 := eq264 x x
       grind)
    | exact resolve eq264 eq230543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq230543
  have eq230598 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq230579
  have eq230601 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq230388
       have i₂ := eq230536
       grind)
    | exact superpose eq230536 eq230388
    | exact resolve eq230388 eq230536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230388 eq230536
  have eq230602 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq230601
       have i₂ := eq230548
       grind)
    | exact superpose eq230548 eq230601
    | exact resolve eq230601 eq230548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230548 eq230601
  have eq230603 : False := by grind
  exact eq230603

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation3880 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq114 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq116 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq580 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq116
    | exact resolve eq116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq608 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq580
    | (have j0 := eq580 X0 X1
       grind)
    | exact resolve eq580 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq619 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq608 X1 X0
       grind)
    | exact superpose eq608 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq608 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq608 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq608 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq608 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq632 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq619 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq633 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq632 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq660 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq633 X0 X1
       grind)
    | exact superpose eq633 eq10
    | (have j1 := eq633 X0 X1
       grind)
    | exact resolve eq10 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq660 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq660
    | (have j0 := eq660 X0 X1
       grind)
    | exact resolve eq660 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq719 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq697 X0 (σ X1)
       grind)
    | exact superpose eq697 eq37
    | (have j1 := eq697 X0 (σ X1)
       grind)
    | exact resolve eq37 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq697
  have eq3399 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq719 (σ X0) X1
       grind)
    | exact superpose eq719 eq28
    | (have j1 := eq719 (σ X0) X1
       grind)
    | exact resolve eq28 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq719
  have eq3444 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3399 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3399
    | (have j0 := eq3399 X0 X1
       grind)
    | exact resolve eq3399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3399
  have eq3476 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3444 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3444
    | (have j0 := eq3444 X0 X1
       grind)
    | exact resolve eq3444 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3444
  have eq3485 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3476 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3476
    | (have j0 := eq3476 X0 X1
       grind)
    | exact resolve eq3476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3476
  have eq3684 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq3485 X1 X0
       grind)
    | exact superpose eq3485 eq11
    | (have j1 := eq3485 X1 X0
       grind)
    | exact resolve eq11 eq3485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3485
  have eq4430 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq5051 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3684 y x
       grind)
    | exact superpose eq3684 eq16
    | (have j1 := eq3684 y x
       grind)
    | exact resolve eq16 eq3684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3684
  have eq5085 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5051
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq5051
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq5051
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5051
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5051 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5087 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq5051
       have i₂ := eq633 x y
       grind)
    | exact superpose eq633 eq5051
    | (have j1 := eq633 x y
       grind)
    | (have r₁ := eq5051
       have r₂ := eq633 x y
       grind)
    | (have r₁ := eq5051
       have r₂ := eq633 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5051
       have r₂ := eq633 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5051 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq5051
  have eq5088 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5087
  have eq5089 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq5088
  have eq5091 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5085
  have eq5092 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq5091
  have eq5095 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5089
       grind)
    | exact superpose eq5089 eq16
    | exact resolve eq16 eq5089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5089
  have eq5096 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5095
       have r₂ := eq22 x
       grind)
    | exact resolve eq5095 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5095
  have eq5101 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4430 x y
       have i₂ := eq5096
       grind)
    | exact superpose eq5096 eq4430
    | (have j0 := eq4430 x y
       grind)
    | exact resolve eq4430 eq5096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4430 eq5096
  have eq5106 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5101
  have eq5107 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5106
  have eq5111 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5092
       grind)
    | exact superpose eq5092 eq16
    | exact resolve eq16 eq5092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5092
  have eq5112 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5111
       have r₂ := eq22 x
       grind)
    | exact resolve eq5111 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5111
  have eq5121 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5107
       grind)
    | exact superpose eq5107 eq16
    | exact resolve eq16 eq5107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5107
  have eq5142 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5121
       have i₂ := eq5112
       grind)
    | exact superpose eq5112 eq5121
    | exact resolve eq5121 eq5112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5112 eq5121
  have eq5145 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq5142
  have eq5146 : (σ x) = (σ y) := by grind
  clear eq5145
  have eq5147 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5146
       grind)
    | exact superpose eq5146 eq16
    | exact resolve eq16 eq5146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5148 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5146
       grind)
    | exact superpose eq5146 eq10
    | exact resolve eq10 eq5146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5146
  have eq5200 : x = y := by
    first
    | (have i₁ := eq5148
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5148
    | exact resolve eq5148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5148
  have eq5201 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5147
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5147
    | exact resolve eq5147 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5147
  have eq5202 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5201
       have i₂ := eq5200
       grind)
    | exact superpose eq5200 eq5201
    | exact resolve eq5201 eq5200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5200 eq5201
  have eq5203 : False := by grind
  exact eq5203

/-- `Equation3887`: `x ◇ x = (y ◇ (y ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation3887 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3887 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3887.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq24
    | exact resolve eq24 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq286 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq289 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq359 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq360 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq359 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq367 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq360 (τ X0)
       grind)
    | exact superpose eq360 eq20
    | exact resolve eq20 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq888 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq289 x y
       grind)
    | exact superpose eq289 eq16
    | (have j1 := eq289 x y
       grind)
    | exact resolve eq16 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq893 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X1) (σ (k X0 X1))) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X1)
       have i₂ := eq289 X1 X0
       grind)
    | exact superpose eq289 eq9
    | (have j1 := eq289 X1 X0
       grind)
    | exact resolve eq9 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq900 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq289 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq900 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq903 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq898 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq910 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq903 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq903
    | (have j0 := eq903 X0
       grind)
    | exact resolve eq903 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq2590 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (σ (k (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq910 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq910
    | exact resolve eq910 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq2627 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2590 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq2590
    | (have j0 := eq2590 X0
       grind)
    | exact resolve eq2590 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590
  have eq2630 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2627 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2627
    | (have j0 := eq2627 X0
       grind)
    | exact resolve eq2627 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2627
  have eq2631 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2630 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq2630
    | (have j0 := eq2630 X0
       grind)
    | exact resolve eq2630 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2630
  have eq2632 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2631 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq2631
    | (have j0 := eq2631 X0
       grind)
    | exact resolve eq2631 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631
  have eq2633 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2632 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2632
    | (have j0 := eq2632 X0
       grind)
    | exact resolve eq2632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2632
  have eq2638 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq2633 X0
       grind)
    | exact superpose eq2633 eq9
    | (have j1 := eq2633 X0
       grind)
    | exact resolve eq9 eq2633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2670 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (k (τ X0) (k (τ X0) (τ X0))) = (M.op (τ X0) (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq367 X0
       have i₂ := eq2638 (τ X0)
       grind)
    | exact superpose eq2638 eq367
    | (have j1 := eq2638 (τ X0)
       grind)
    | exact resolve eq367 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq2638
  have eq2676 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (k (τ X0) (k (τ X0) (τ X0))) = (M.op (τ X0) (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2670 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2670
    | (have j0 := eq2670 X0
       grind)
    | exact resolve eq2670 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2670
  have eq2678 : ∀ X0 : G, (k (τ X0) (τ (k X0 X0))) = (M.op (τ X0) (τ (k X0 X0))) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2676 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq2676
    | (have j0 := eq2676 X0
       grind)
    | exact resolve eq2676 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676
  have eq2680 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (τ (k X0 (k X0 X0))) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2678 X0
       have i₂ := eq33 (k X0 X0) X0
       grind)
    | exact superpose eq33 eq2678
    | (have j0 := eq2678 X0
       grind)
    | exact resolve eq2678 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2678
  have eq4024 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq286 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq286
    | exact resolve eq286 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq4072 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4024 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4024
    | (have j0 := eq4024 X0 X1
       grind)
    | exact resolve eq4024 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4024
  have eq4507 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq285 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq285
    | exact resolve eq285 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq4591 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4507 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq4507
    | (have j0 := eq4507 X0 X1
       grind)
    | exact resolve eq4507 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4507
  have eq6745 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq888
       have i₂ := eq4072 x y
       grind)
    | exact superpose eq4072 eq888
    | (have j1 := eq4072 (σ x) (σ y)
       grind)
    | (have r₁ := eq888
       have r₂ := eq4072 x y
       grind)
    | exact resolve eq888 eq4072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq4072
  have eq6746 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq6745
  have eq11007 : ∀ X0 : G, (τ (k (σ X0) (k (σ X0) (σ X0)))) = (M.op (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (σ X0) = (k (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2680 (σ X0)
       have i₂ := eq30 X0 (σ X0)
       grind)
    | exact superpose eq30 eq2680
    | (have j0 := eq2680 (σ X0)
       grind)
    | exact resolve eq2680 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2680
  have eq11023 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (τ (k (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (k (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11007 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11007
    | (have j0 := eq11007 X0
       grind)
    | exact resolve eq11007 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11007
  have eq11049 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (σ X0) = (k (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11023 X0
       have i₂ := eq35 X0 (σ X0) (σ X0)
       grind)
    | exact superpose eq35 eq11023
    | (have j0 := eq11023 X0
       grind)
    | exact resolve eq11023 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq11023
  have eq11069 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (σ X0) = (k (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11049 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11049
    | (have j0 := eq11049 X0
       grind)
    | exact resolve eq11049 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11049
  have eq11087 : ∀ X0 : G, (σ X0) = (σ (k (M.op (τ (σ X0)) (τ (σ X0))) X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11069 X0
       have i₂ := eq15 (M.op (τ (σ X0)) (τ (σ X0))) X0
       grind)
    | exact superpose eq15 eq11069
    | (have j0 := eq11069 X0
       grind)
    | exact resolve eq11069 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11069
  have eq11105 : ∀ X0 : G, (σ X0) = (σ (k (M.op X0 X0) X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11087 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11087
    | (have j0 := eq11087 X0
       grind)
    | exact resolve eq11087 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11087
  have eq11123 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11105 X0
       have i₂ := eq360 X0
       grind)
    | exact superpose eq360 eq11105
    | (have j0 := eq11105 X0
       grind)
    | exact resolve eq11105 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11105
  have eq11153 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11123 X0
       have i₂ := eq2633 X0
       grind)
    | exact superpose eq2633 eq11123
    | (have j0 := eq11123 X0
       have j1 := eq2633 X0
       grind)
    | exact resolve eq11123 eq2633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633
  have eq11208 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq11153 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11153
  have eq11263 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k (M.op X0 X0) X1)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X0) X1
       have i₂ := eq11208 X0
       grind)
    | exact superpose eq11208 eq15
    | (have j1 := eq11208 X0
       grind)
    | exact resolve eq15 eq11208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11208
  have eq11342 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (M.op X0 X0) X1)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11263 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq11263
    | (have j0 := eq11263 X0 X1
       grind)
    | exact resolve eq11263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11263
  have eq12050 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (k X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11342 X0 X0
       have i₂ := eq360 X0
       grind)
    | exact superpose eq360 eq11342
    | (have j0 := eq11342 X0 x
       grind)
    | exact resolve eq11342 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11342
  have eq13032 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11123 X0
       have i₂ := eq12050 X0
       grind)
    | exact superpose eq12050 eq11123
    | (have j0 := eq11123 X0
       have j1 := eq12050 X0
       grind)
    | exact resolve eq11123 eq12050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11123 eq12050
  have eq13079 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13032 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13032
  have eq13180 : ∀ X0 : G, (k X0 (σ (k (τ X0) (τ X0)))) = (σ (M.op (τ X0) (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq13079 (τ X0)
       grind)
    | exact superpose eq13079 eq19
    | (have j1 := eq13079 (τ X0)
       grind)
    | exact resolve eq19 eq13079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq13079
  have eq13231 : ∀ X0 : G, (k X0 (σ (τ (k X0 X0)))) = (σ (M.op (τ X0) (τ (k X0 X0)))) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13180 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq13180
    | (have j0 := eq13180 X0
       grind)
    | exact resolve eq13180 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13180
  have eq13289 : ∀ X0 : G, (k X0 (k X0 X0)) = (σ (M.op (τ X0) (τ (k X0 X0)))) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13231 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq13231
    | (have j0 := eq13231 X0
       grind)
    | exact resolve eq13231 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13231
  have eq13340 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (k X0 (k X0 X0)) = (σ (M.op (τ X0) (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq13289 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq13289
    | (have j0 := eq13289 X0
       grind)
    | exact resolve eq13289 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13289
  have eq13389 : ∀ X0 : G, (k X0 (k X0 X0)) = (σ (M.op (τ X0) (τ (k X0 X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13340 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13340
    | (have j0 := eq13340 X0
       grind)
    | exact resolve eq13340 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13340
  have eq13571 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13389 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq13389
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq13389 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13389
  have eq13648 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13571 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13571
  have eq13670 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    grind
  clear eq13648
  have eq14017 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op (τ (σ X0)) (τ (σ (k X0 X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13670 (σ x)
       have i₂ := eq289 x x
       grind)
    | exact superpose eq289 eq13670
    | (have j0 := eq13670 (σ X0)
       have j1 := eq289 X0 X0
       grind)
    | exact resolve eq13670 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13670
  have eq14059 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op (τ (σ X0)) (τ (σ (k X0 X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq14017 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14017
  have eq14075 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op (τ (σ X0)) (τ (σ (k X0 X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq14059 X0
       have j1 := eq901 X0
       grind)
    | (have r₁ := eq14059 X0
       have r₂ := eq901 X0
       grind)
    | exact resolve eq14059 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14059
  have eq14086 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op (τ (σ X0)) (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14075 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq14075
    | (have j0 := eq14075 X0
       grind)
    | exact resolve eq14075 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14075
  have eq14087 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14086 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14086
    | (have j0 := eq14086 X0
       grind)
    | exact resolve eq14086 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14086
  have eq25093 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq893 X0 X0
       have i₂ := eq14087 X0
       grind)
    | exact superpose eq14087 eq893
    | (have j0 := eq893 X0 X0
       have j1 := eq14087 X0
       grind)
    | exact resolve eq893 eq14087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq14087
  have eq25102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq25093 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25093
  have eq47746 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ X0) (k (τ X0) (τ X0)))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25102 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25102
    | exact resolve eq25102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47791 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ (k X0 X0)))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq47746 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq47746
    | (have j0 := eq47746 X0
       grind)
    | exact resolve eq47746 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq47746
  have eq47875 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ (M.op X0 X0)))) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq47791 X0
       have i₂ := eq4591 X0 X0
       grind)
    | exact superpose eq4591 eq47791
    | (have j0 := eq47791 X0
       have j1 := eq4591 X0 X0
       grind)
    | exact resolve eq47791 eq4591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4591 eq47791
  have eq47918 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ (M.op X0 X0)))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq47875 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47875
  have eq48024 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (M.op (τ (σ X0)) (τ (σ (k X0 X0))))) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq47918 (σ x)
       have i₂ := eq289 x x
       grind)
    | exact superpose eq289 eq47918
    | (have j0 := eq47918 (σ X0)
       have j1 := eq289 X0 X0
       grind)
    | exact resolve eq47918 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq47918
  have eq48053 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (M.op (τ (σ X0)) (τ (σ (k X0 X0))))) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq48024 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48024
  have eq48066 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (M.op (τ (σ X0)) (τ (σ (k X0 X0))))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq48053 X0
       have j1 := eq901 X0
       grind)
    | (have r₁ := eq48053 X0
       have r₂ := eq901 X0
       grind)
    | exact resolve eq48053 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq48053
  have eq48072 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (M.op (τ (σ X0)) (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq48066 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq48066
    | (have j0 := eq48066 X0
       grind)
    | exact resolve eq48066 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48066
  have eq48076 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (M.op X0 (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq48072 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48072
    | (have j0 := eq48072 X0
       grind)
    | exact resolve eq48072 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48072
  have eq48169 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq25102 X0
       have i₂ := eq48076 X0
       grind)
    | exact superpose eq48076 eq25102
    | (have j0 := eq25102 X0
       have j1 := eq48076 X0
       grind)
    | exact resolve eq25102 eq48076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25102 eq48076
  have eq48179 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq48169 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48169
  have eq48284 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq360 (σ X0)
       have i₂ := eq48179 X0
       grind)
    | exact superpose eq48179 eq360
    | (have j1 := eq48179 X0
       grind)
    | exact resolve eq360 eq48179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48179
  have eq48347 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48284 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq48284
    | (have j0 := eq48284 X0
       grind)
    | exact resolve eq48284 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48284
  have eq48348 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq48347 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48347
  have eq48411 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq48348 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48348
    | exact resolve eq48348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48509 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    grind
  have eq48514 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq360 (σ X0)
       have i₂ := eq48348 X0
       grind)
    | exact superpose eq48348 eq360
    | exact resolve eq360 eq48348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48709 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq48514 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq48514
    | exact resolve eq48514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48514
  have eq48711 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq48509 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq48509
    | exact resolve eq48509 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48509
  have eq48783 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq48411 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq48411
    | exact resolve eq48411 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq48411
  have eq48926 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq48783 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48783
    | exact resolve eq48783 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48783
  have eq50440 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq48709 X0
       have i₂ := eq48926 X0
       grind)
    | exact superpose eq48926 eq48709
    | exact resolve eq48709 eq48926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48709
  have eq50627 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50440 X0
       have i₂ := eq360 X0
       grind)
    | exact superpose eq360 eq50440
    | exact resolve eq50440 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq50440
  have eq50986 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq48711 X0
       have i₂ := eq48926 X0
       grind)
    | exact superpose eq48926 eq48711
    | exact resolve eq48711 eq48926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48711
  have eq51079 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq50986
  have eq585244 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq51079 x
       have i₂ := eq6746
       grind)
    | exact superpose eq6746 eq51079
    | exact resolve eq51079 eq6746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6746
  have eq585338 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq585244
       have r₂ := eq16
       grind)
    | exact resolve eq585244 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585244
  have eq585698 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq585338
       have i₂ := eq48348 y
       grind)
    | exact superpose eq48348 eq585338
    | exact resolve eq585338 eq48348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585338
  have eq585994 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq585698
       have i₂ := eq48926 y
       grind)
    | exact superpose eq48926 eq585698
    | exact resolve eq585698 eq48926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585698
  have eq586276 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq585994
       have i₂ := eq48348 x
       grind)
    | exact superpose eq48348 eq585994
    | exact resolve eq585994 eq48348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48348 eq585994
  have eq586506 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq586276
       have i₂ := eq48926 x
       grind)
    | exact superpose eq48926 eq586276
    | exact resolve eq586276 eq48926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48926 eq586276
  have eq587048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq50627 y
       have i₂ := eq586506
       grind)
    | exact superpose eq586506 eq50627
    | exact resolve eq50627 eq586506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586506
  have eq587105 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq587048
       have r₂ := eq16
       grind)
    | exact resolve eq587048 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587048
  have eq587468 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq587105
       grind)
    | exact superpose eq587105 eq10
    | exact resolve eq10 eq587105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587105
  have eq587958 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq587468
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq587468
    | exact resolve eq587468 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587468
  have eq588710 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq51079 x
       have i₂ := eq587958
       grind)
    | exact superpose eq587958 eq51079
    | exact resolve eq51079 eq587958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51079 eq587958
  have eq588762 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq588710
       have r₂ := eq16
       grind)
    | exact resolve eq588710 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588710
  have eq589106 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq588762
       grind)
    | exact superpose eq588762 eq10
    | exact resolve eq10 eq588762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588762
  have eq589597 : x = (M.op y y) := by
    first
    | (have i₁ := eq589106
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq589106
    | exact resolve eq589106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589106
  have eq590450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50627 y
       have i₂ := eq589597
       grind)
    | exact superpose eq589597 eq50627
    | exact resolve eq50627 eq589597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50627 eq589597
  have eq590508 : False := by grind
  exact eq590508

/-- `Equation3897`: `x ◇ x = (y ◇ (z ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation3897 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3897 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3897.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq266 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq274 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq266
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq266
    | exact resolve eq266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq526 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq272 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq272
    | (have j0 := eq272 (σ X1) (σ X0)
       grind)
    | exact resolve eq272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ X0)) ∨ (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq272 (τ X0) X1
       grind)
    | exact superpose eq272 eq18
    | (have j1 := eq272 (τ X0) X1
       grind)
    | exact resolve eq18 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq272
  have eq7518 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq274
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq274
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq274 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7519 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq7518
  have eq20149 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq537 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq537
    | exact resolve eq537 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq20303 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20149 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq20149
    | (have j0 := eq20149 X0 X1
       grind)
    | exact resolve eq20149 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20149
  have eq128651 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq526 y x
       have i₂ := eq7519
       grind)
    | exact superpose eq7519 eq526
    | (have j0 := eq526 y x
       grind)
    | exact resolve eq526 eq7519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7519
  have eq128659 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq128651
  have eq128665 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq128659
       have r₂ := eq274
       grind)
    | exact resolve eq128659 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128659
  have eq128668 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq128665
       have r₂ := eq16
       grind)
    | exact resolve eq128665 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128665
  have eq128671 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq274
       have i₂ := eq128668
       grind)
    | exact superpose eq128668 eq274
    | exact resolve eq274 eq128668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq128673 : x ≠ y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq128668
       grind)
    | exact superpose eq128668 eq12
    | exact resolve eq12 eq128668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128674 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq128668
       grind)
    | exact superpose eq128668 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq128668
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq128668
       grind)
    | exact resolve eq13 eq128668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128668
  have eq128751 : x = y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq128674
  have eq128752 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq128671
  have eq128772 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq128673
       have r₂ := eq128751
       grind)
    | exact resolve eq128673 eq128751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128673 eq128751
  have eq128789 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq526 y x
       have i₂ := eq128772
       grind)
    | exact superpose eq128772 eq526
    | (have j0 := eq526 y x
       grind)
    | exact resolve eq526 eq128772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq128772
  have eq128845 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq128789
  have eq128854 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq128845
       have r₂ := eq128752
       grind)
    | exact resolve eq128845 eq128752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128752 eq128845
  have eq128891 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq128854
       grind)
    | exact superpose eq128854 eq12
    | exact resolve eq12 eq128854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128892 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq128854
       grind)
    | exact superpose eq128854 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq128854
       grind)
    | exact resolve eq13 eq128854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128965 : (σ y) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq128854
  have eq128970 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq128892
  have eq129032 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq128970
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq128970
    | exact resolve eq128970 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128970
  have eq129033 : (σ y) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq128891
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq128891
    | exact resolve eq128891 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128891
  have eq129091 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq129032
       have r₂ := eq128965
       grind)
    | exact resolve eq129032 eq128965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129032
  have eq129092 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq129033
       have r₂ := eq128965
       grind)
    | exact resolve eq129033 eq128965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128965 eq129033
  have eq129133 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq129092
       have r₂ := eq129091
       grind)
    | exact resolve eq129092 eq129091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129091 eq129092
  have eq129159 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq129133
       grind)
    | exact superpose eq129133 eq16
    | exact resolve eq16 eq129133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129133
  have eq129495 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq129159
       have i₂ := eq20303 x y
       grind)
    | exact superpose eq20303 eq129159
    | (have j1 := eq20303 x y
       grind)
    | (have r₁ := eq129159
       have r₂ := eq20303 x y
       grind)
    | exact resolve eq129159 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20303
  have eq129496 : x = (k y x) ∨ y = (M.op x y) := by grind
  clear eq129495
  have eq129514 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq129159
       have i₂ := eq129496
       grind)
    | exact superpose eq129496 eq129159
    | exact resolve eq129159 eq129496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129496
  have eq129630 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq129514
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq129514
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq129514 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129514
  have eq129631 : x = y ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq129630
  have eq129632 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq271 x y
       grind)
    | (have r₁ := eq129631
       have r₂ := eq271 x y
       grind)
    | (have r₁ := eq129631
       have r₂ := eq271 y x
       grind)
    | (have r₁ := eq129631
       have r₂ := eq271 y (M.op x y)
       grind)
    | exact resolve eq129631 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq129631
  have eq129722 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq129159
       have i₂ := eq129632
       grind)
    | exact superpose eq129632 eq129159
    | exact resolve eq129159 eq129632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129632
  have eq129734 : y = (M.op x y) := by grind
  clear eq129722
  have eq129758 : x ≠ y ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq129734
       grind)
    | exact superpose eq129734 eq12
    | exact resolve eq12 eq129734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129759 : y ≠ y ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq129734
       grind)
    | exact superpose eq129734 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq129734
       grind)
    | exact resolve eq13 eq129734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129836 : x = y ∨ y = (k y x) := by grind
  clear eq129759
  have eq129855 : y = (k y x) := by
    first
    | (have r₁ := eq129758
       have r₂ := eq129836
       grind)
    | exact resolve eq129758 eq129836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129758 eq129836
  have eq129872 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq129159
       have i₂ := eq129855
       grind)
    | exact superpose eq129855 eq129159
    | exact resolve eq129159 eq129855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129159 eq129855
  have eq129941 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq129872
       have i₂ := eq129734
       grind)
    | exact superpose eq129734 eq129872
    | exact resolve eq129872 eq129734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129734 eq129872
  have eq129942 : False := by grind
  exact eq129942

/-- `Equation3912`: `x ◇ x = (y ◇ (z ◇ w)) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_pyy_pxy_Equation3912 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X3)) X3) := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq133 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq50
    | (have j0 := eq50 (M.op x y)
       grind)
    | exact resolve eq50 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq176 : ∀ X0 X1 X2 X5 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X0)) X5) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq16 X1 X2 (M.op x (M.op x X5)) X5
       have i₂ := eq16 X0 x x X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op x y)) y) := by
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
  have eq178 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X5 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq16 X1 (M.op x (M.op x (M.op x X5))) x X5
       have i₂ := eq16 X0 x x (M.op x X5)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq180 X3 x X4
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq180 X0 (M.op X0 X0) x
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op x y)) y) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 x X3
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq177 (M.op X0 X0) X1
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq177
    | exact resolve eq177 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq257 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 x X3
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq178 (M.op X0 X0) X1
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq482 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq398 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq398
    | exact resolve eq398 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq585 : ∀ X0 : G, (τ (k (k (σ y) (σ y)) X0)) = (k (k y y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq115 eq482
    | exact resolve eq482 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X1) X2) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 X1
       have i₂ := eq180 X0 X1 x
       grind)
    | (have i₁ := eq183 (M.op X0 X0)
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq183
    | exact resolve eq183 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq183 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq183
    | exact resolve eq183 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq1572 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (k (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X0 X2 X1 X3
       have i₂ := eq695 X0 X1
       grind)
    | exact superpose eq695 eq176
    | exact resolve eq176 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1598 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X1 X2 (M.op X0 X0)
       have i₂ := eq695 X0 (M.op X1 X1)
       grind)
    | exact superpose eq695 eq180
    | exact resolve eq180 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1752 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq11
    | (have j0 := eq11 X0 (k X1 X1)
       grind)
    | exact resolve eq11 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1843 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq1844 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq1875 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1752 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752
  have eq2021 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op x y)) y) = (M.op (k (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq256 x (M.op x x) X3
       have i₂ := eq1572 X0 X1 (M.op x x) X2
       grind)
    | exact superpose eq1572 eq256
    | exact resolve eq256 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq2023 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X4) X5) = (M.op (k (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq230 x (M.op x x) X4 X5
       have i₂ := eq1572 X0 X1 (M.op x x) X2
       grind)
    | exact superpose eq1572 eq230
    | exact resolve eq230 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq1572
  have eq2420 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (σ x) (σ y))) (σ y)) = (k X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X1 X2
       have i₂ := eq1875 X1 X0
       grind)
    | exact superpose eq1875 eq178
    | (have j1 := eq1875 X1 X0
       grind)
    | exact resolve eq178 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2421 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (k X0 X0) X3) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq180 X2 X1 X3
       have i₂ := eq1875 X2 X0
       grind)
    | exact superpose eq1875 eq180
    | (have j1 := eq1875 X1 (M.op (k X0 X0) X3)
       grind)
    | exact resolve eq180 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2422 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (k X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq180 X2 X1 X3
       have i₂ := eq1875 X1 X0
       grind)
    | exact superpose eq1875 eq180
    | (have j1 := eq1875 X1 X0
       grind)
    | exact resolve eq180 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2424 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X1 X2
       have i₂ := eq1875 X2 X0
       grind)
    | exact superpose eq1875 eq181
    | (have j1 := eq1875 X1 X0
       grind)
    | exact resolve eq181 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2480 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1875 X0 (σ X1)
       grind)
    | exact superpose eq1875 eq10
    | (have j1 := eq1875 X0 (σ (k X1 X1))
       grind)
    | exact resolve eq10 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2483 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1875 X0 (τ X1)
       grind)
    | exact superpose eq1875 eq34
    | (have j1 := eq1875 X0 (τ X1)
       grind)
    | exact resolve eq34 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2487 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2483 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq2483
    | (have j0 := eq2483 X0 X1
       grind)
    | exact resolve eq2483 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2483
  have eq2619 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ X1))) ∨ (σ X1) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq455 X1 (σ X1)
       have i₂ := eq2424 (σ X1) X0 X2
       grind)
    | exact superpose eq2424 eq455
    | (have j1 := eq2424 (σ X1) X1 X2
       grind)
    | exact resolve eq455 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2621 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) ∨ (τ X1) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq2424 (τ X1) X0 X2
       grind)
    | exact superpose eq2424 eq34
    | (have j1 := eq2424 (τ X1) X1 X2
       grind)
    | exact resolve eq34 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq2625 : ∀ X0 X1 X2 : G, (k X1 X1) = (σ (M.op X0 X0)) ∨ (τ X1) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2621 X0 X1 X2
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq2621
    | (have j0 := eq2621 X0 X1 X2
       grind)
    | exact resolve eq2621 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2621
  have eq2626 : ∀ X0 X1 X2 : G, (k X1 X1) = (τ (M.op X0 X0)) ∨ (σ X1) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2619 X0 X1 X2
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq2619
    | (have j0 := eq2619 X0 X1 X2
       grind)
    | exact resolve eq2619 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619
  have eq9465 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1843
       grind)
    | exact superpose eq1843 eq40
    | exact resolve eq40 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq9466 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9465
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9465
    | exact resolve eq9465 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9465
  have eq9468 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq9466
    | exact resolve eq9466 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9466
  have eq33107 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (k y y) (τ (k (σ y) (σ y)))) ∨ (M.op X0 X0) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq585 (k sF3 sF3)
       have i₂ := eq1875 X0 (k sF3 sF3)
       grind)
    | exact superpose eq1875 eq585
    | (have j1 := eq1875 X0 (σ y)
       grind)
    | exact resolve eq585 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33134 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (k y y) (k y y)) ∨ (M.op X0 X0) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq115 eq33107
    | (have j0 := eq33107 X0
       grind)
    | exact resolve eq33107 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33107
  have eq33140 : ∀ X0 : G, (τ (σ y)) = (k (k y y) (k y y)) ∨ (M.op X0 X0) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq1875 eq33134
    | (have j0 := eq33134 X0
       have j1 := eq1875 X0 (σ y)
       grind)
    | exact resolve eq33134 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875 eq33134
  have eq33143 : ∀ X0 : G, y = (k (k y y) (k y y)) ∨ (M.op X0 X0) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq31 eq33140
    | (have j0 := eq33140 X0
       grind)
    | exact resolve eq33140 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33140
  have eq44961 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2421 X1 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421
  have eq45023 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44961 X2 X1 (k X1 X1)
       have i₂ := eq181 (k X1 X1) X0
       grind)
    | (have i₁ := eq44961 X2 X1 (k X1 X1)
       have i₂ := eq181 X0 (k X1 X1)
       grind)
    | exact superpose eq181 eq44961
    | (have j0 := eq44961 X2 X1 X2
       grind)
    | (have r₁ := eq44961 X0 (M.op X1 X1) (k (M.op X1 X1) (M.op X1 X1))
       have r₂ := eq181 (k (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq44961 X0 (M.op X0 X0) (k (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq181 X0 (k (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq44961 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44961
  have eq48042 : ∀ X0 X1 X2 : G, (k (k y y) (τ (k (σ y) (σ y)))) = (τ (M.op (M.op X0 X0) X1)) ∨ (k (σ y) (σ y)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq585 (k sF3 sF3)
       have i₂ := eq2422 (k sF3 sF3) X1 X2 x
       grind)
    | exact superpose eq2422 eq585
    | (have j1 := eq2422 (k (σ y) (σ y)) X2 X2 x
       grind)
    | exact resolve eq585 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq48053 : ∀ X0 X1 X2 : G, (k (k y y) (k y y)) = (τ (M.op (M.op X0 X0) X1)) ∨ (k (σ y) (σ y)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq115 eq48042
    | (have j0 := eq48042 X0 X1 X2
       grind)
    | exact resolve eq48042 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq48042
  have eq48145 : ∀ X0 X1 X2 : G, y = (τ (M.op (M.op X0 X0) X1)) ∨ (k (σ y) (σ y)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq33143 eq48053
    | (have j0 := eq48053 X0 X1 X2
       have j1 := eq33143 X2
       grind)
    | exact resolve eq48053 eq33143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33143 eq48053
  have eq48174 : ∀ X1 X2 : G, (k (σ y) (σ y)) = (M.op X2 X2) ∨ y = (τ (M.op (σ y) X1)) := by
    intro X1 X2
    first
    | exact superpose eq2424 eq48145
    | (have j0 := eq48145 x X1 X2
       have j1 := eq2424 (σ y) X2 X2
       grind)
    | exact resolve eq48145 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48145
  have eq54165 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2480 X1 (M.op X2 X2)
       have i₂ := eq1598 X2 X2 X0
       grind)
    | exact superpose eq1598 eq2480
    | (have j0 := eq2480 X1 (M.op X0 X0)
       grind)
    | exact resolve eq2480 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598 eq2480
  have eq55075 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq2487 X0 (σ X1)
       grind)
    | exact superpose eq2487 eq10
    | (have j1 := eq2487 X0 (σ X1)
       grind)
    | exact resolve eq10 eq2487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2487
  have eq55245 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55075 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq55075
    | (have j0 := eq55075 X0 X1
       grind)
    | exact resolve eq55075 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55075
  have eq65805 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (k X1 X1)) ∨ (M.op X2 X2) = (τ (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq2625 X0 (σ X1) X2
       grind)
    | exact superpose eq2625 eq10
    | (have j1 := eq2625 X0 (σ X1) X2
       grind)
    | exact resolve eq10 eq2625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2625
  have eq65988 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (k X1 X1)) ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65805 X0 X1 X2
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq65805
    | (have j0 := eq65805 X0 X1 X2
       grind)
    | exact resolve eq65805 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65805
  have eq66393 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (τ (k X1 X1)) ∨ (M.op X2 X2) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq482 X1 X1
       have i₂ := eq2626 X0 (τ X1) X2
       grind)
    | exact superpose eq2626 eq482
    | (have j1 := eq2626 X0 (τ X1) X2
       grind)
    | exact resolve eq482 eq2626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482 eq2626
  have eq66488 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (τ (k X1 X1)) ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66393 X0 X1 X2
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq66393
    | (have j0 := eq66393 X0 X1 X2
       grind)
    | exact resolve eq66393 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66393
  have eq68052 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X1) = X2 ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55245 X0 X2
       have i₂ := eq55245 X1 X2
       grind)
    | exact superpose eq55245 eq55245
    | (have j0 := eq55245 X1 X2
       have j1 := eq55245 X1 X2
       grind)
    | exact resolve eq55245 eq55245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55245
  have eq68469 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq68052 X0 X1 X2
       have j1 := eq45023 X0 X2 X1
       grind)
    | (have r₁ := eq68052 X0 X0 X1
       have r₂ := eq45023 X0 X1 X2
       grind)
    | (have r₁ := eq68052 X0 X1 (M.op X0 X0)
       have r₂ := eq45023 X0 (M.op X1 X1) X2
       grind)
    | (have r₁ := eq68052 X0 X1 X1
       have r₂ := eq45023 X0 X1 X2
       grind)
    | exact resolve eq68052 eq45023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68052
  have eq76192 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X1 X1)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq68469 X0 X1 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76193 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq68469 X0 X0 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68469
  have eq76196 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq76193 X0 x
       have j1 := eq54165 X0 X0 X0
       grind)
    | (have r₁ := eq76193 x X0
       have r₂ := eq54165 X0 x x
       grind)
    | (have r₁ := eq76193 x x
       have r₂ := eq54165 X0 x x
       grind)
    | exact resolve eq76193 eq54165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76193
  have eq76197 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq76192 X0 X1
       have j1 := eq54165 X0 X1 X0
       grind)
    | (have r₁ := eq76192 X0 X0
       have r₂ := eq54165 X0 X0 x
       grind)
    | (have r₁ := eq76192 X0 x
       have r₂ := eq54165 X0 x x
       grind)
    | exact resolve eq76192 eq54165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54165 eq76192
  have eq76482 : ∀ X0 X2 : G, (k X0 X0) = (σ (k X0 X0)) ∨ (M.op X2 X2) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq76196 (M.op X2 X2)
       have i₂ := eq2422 X0 x X2 (M.op X2 X2)
       grind)
    | exact superpose eq2422 eq76196
    | (have j1 := eq2422 X0 X2 X2 x
       grind)
    | exact resolve eq76196 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422
  have eq76535 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65988 X0 X1 X2
       have i₂ := eq76196 X0
       grind)
    | exact superpose eq76196 eq65988
    | (have j0 := eq65988 X0 (σ (k X1 X1)) X0
       grind)
    | exact resolve eq65988 eq76196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65988
  have eq76540 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op X0 X0)
       have i₂ := eq76196 X0
       grind)
    | exact superpose eq76196 eq15
    | exact resolve eq15 eq76196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76948 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76197 (k (M.op x x) x) X2
       have i₂ := eq2023 x x (k (M.op x x) x) X0 X1
       grind)
    | exact superpose eq2023 eq76197
    | exact resolve eq76197 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76949 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq76197 (k (M.op x x) x) X1
       have i₂ := eq2021 x x (k (M.op x x) x) X0
       grind)
    | exact superpose eq2021 eq76197
    | exact resolve eq76197 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021
  have eq77116 : ∀ X0 X2 X3 : G, (τ (k X2 X2)) = (τ (σ (M.op X0 X0))) ∨ (M.op X3 X3) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq66488 x X2 X3
       have i₂ := eq76197 X0 x
       grind)
    | exact superpose eq76197 eq66488
    | (have j0 := eq66488 X0 X2 X3
       grind)
    | exact resolve eq66488 eq76197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66488
  have eq77273 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X1 X1)
       have i₂ := eq76197 X1 X0
       grind)
    | exact superpose eq76197 eq15
    | exact resolve eq15 eq76197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76197
  have eq77493 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (τ (k X2 X2)) ∨ (M.op X3 X3) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq77116 X0 X2 X3
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq77116
    | (have j0 := eq77116 X0 (τ (k X2 X2)) X0
       grind)
    | exact resolve eq77116 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77116
  have eq78251 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (τ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77273 (k (M.op x x) x) X2
       have i₂ := eq2023 x x (k (M.op x x) x) X0 X1
       grind)
    | exact superpose eq2023 eq77273
    | exact resolve eq77273 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023
  have eq178181 : ∀ X0 : G, (k x x) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq39 x
       have i₂ := eq76482 x X0
       grind)
    | exact superpose eq76482 eq39
    | (have j1 := eq76482 x X0
       grind)
    | exact resolve eq39 eq76482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178305 : ∀ X0 : G, (k x x) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq178181 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq178181
    | (have j0 := eq178181 X0
       grind)
    | exact resolve eq178181 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178181
  have eq214172 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op x y) (M.op x y)) ∨ (M.op X1 X1) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq133
       have i₂ := eq77493 X0 sF1 x
       grind)
    | exact superpose eq77493 eq133
    | (have j1 := eq77493 X0 (k (M.op x y) (M.op x y)) X0
       grind)
    | exact resolve eq133 eq77493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq77493
  have eq214232 : ∀ X0 : G, (M.op X0 X0) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2424 eq214172
    | (have j0 := eq214172 X0 x
       have j1 := eq2424 (M.op x y) X0 x
       grind)
    | exact resolve eq214172 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214172
  have eq217015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1844 eq9468
    | exact resolve eq9468 eq1844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1844 eq9468
  have eq217030 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq217015
       have r₂ := eq27
       grind)
    | exact resolve eq217015 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217015
  have eq217035 : y = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2424 eq217030
    | (have j1 := eq2424 x x y
       grind)
    | exact resolve eq217030 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217030
  have eq217038 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2424 eq217035
    | (have j1 := eq2424 x x y
       grind)
    | exact resolve eq217035 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424 eq217035
  have eq217847 : (τ (σ y)) = (k x x) ∨ x = (M.op y y) ∨ y = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq217038 eq97
    | exact resolve eq97 eq217038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217038
  have eq217936 : y = (k x x) ∨ x = (M.op y y) ∨ y = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq31 eq217847
    | exact resolve eq217847 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq217847
  have eq217958 : y = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq178305 eq217936
    | (have j1 := eq178305 y
       grind)
    | exact resolve eq217936 eq178305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178305 eq217936
  have eq217959 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (k (σ x) (σ x)) := by grind
  clear eq217958
  have eq218151 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ x = (M.op y y) ∨ y = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq217959 eq77273
    | exact resolve eq77273 eq217959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217959
  have eq218311 : ∀ X0 : G, (M.op X0 X0) = x ∨ x = (M.op y y) ∨ y = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq29 eq218151
    | exact resolve eq218151 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218151
  have eq218500 : y = (k (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq218311 y
       have j1 := eq45023 x x y
       grind)
    | (have r₁ := eq218311 x
       have r₂ := eq45023 x x x
       grind)
    | (have r₁ := eq218311 x
       have r₂ := eq45023 y x x
       grind)
    | exact resolve eq218311 eq45023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218311
  have eq218644 : (k x x) = (τ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq218500 eq97
    | exact resolve eq97 eq218500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq218500
  have eq218833 : ∀ X0 : G, (τ y) = (σ (τ y)) ∨ (M.op X0 X0) = x ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq76482 x x
       have i₂ := eq218644
       grind)
    | exact superpose eq218644 eq76482
    | (have j0 := eq76482 x X0
       grind)
    | exact resolve eq76482 eq218644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76482
  have eq218834 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ y)) ∨ (M.op X1 X1) = x ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq76535 X0 x X1
       have i₂ := eq218644
       grind)
    | exact superpose eq218644 eq76535
    | (have j0 := eq76535 X0 (σ (τ y)) X0
       grind)
    | exact resolve eq76535 eq218644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76535 eq218644
  have eq218845 : ∀ X0 : G, (M.op X0 X0) = (σ (τ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq218834 X0 y
       have j1 := eq45023 X0 (σ (τ y)) X0
       grind)
    | (have r₁ := eq218834 X0 x
       have r₂ := eq45023 X0 (σ (τ y)) x
       grind)
    | (have r₁ := eq218834 X0 X0
       have r₂ := eq45023 X0 x x
       grind)
    | (have r₁ := eq218834 X0 x
       have r₂ := eq45023 y x x
       grind)
    | exact resolve eq218834 eq45023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218834
  have eq218846 : (τ y) = (σ (τ y)) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq218833 y
       have j1 := eq45023 x x y
       grind)
    | (have r₁ := eq218833 x
       have r₂ := eq45023 x x x
       grind)
    | (have r₁ := eq218833 x
       have r₂ := eq45023 y x x
       grind)
    | exact resolve eq218833 eq45023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218833
  have eq218878 : ∀ X0 : G, x = (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq218845 X0
       have i₂ := eq14 y
       grind)
    | exact superpose eq14 eq218845
    | exact resolve eq218845 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218845
  have eq218879 : x = (M.op y y) ∨ y = (τ y) := by
    first
    | (have i₁ := eq218846
       have i₂ := eq14 y
       grind)
    | exact superpose eq14 eq218846
    | exact resolve eq218846 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218846
  have eq218928 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x X1) ∨ y = (τ y) := by
    intro X0 X1
    first
    | (have i₁ := eq180 y X0 X1
       have i₂ := eq218879
       grind)
    | exact superpose eq218879 eq180
    | exact resolve eq180 eq218879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq218930 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (τ y) := by
    intro X0
    first
    | (have i₁ := eq181 X0 y
       have i₂ := eq218879
       grind)
    | exact superpose eq218879 eq181
    | exact resolve eq181 eq218879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq219046 : x = (σ x) ∨ y = (τ y) := by
    first
    | (have i₁ := eq76196 y
       have i₂ := eq218879
       grind)
    | exact superpose eq218879 eq76196
    | exact resolve eq76196 eq218879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218879
  have eq219193 : y = (τ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq219046
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq219046
    | exact resolve eq219046 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219046
  have eq219268 : ∀ X1 : G, x = (M.op x X1) ∨ y = (τ y) := by
    intro X1
    first
    | exact superpose eq218930 eq218928
    | exact resolve eq218928 eq218930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218928
  have eq219370 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ y = (τ y) := by
    intro X1
    first
    | exact superpose eq219193 eq219268
    | exact resolve eq219268 eq219193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219268
  have eq219537 : y = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq219193
       grind)
    | exact superpose eq219193 eq14
    | exact resolve eq14 eq219193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219582 : y = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq219537
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq219537
    | exact resolve eq219537 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219537
  have eq219587 : (M.op x y) = (M.op x (σ y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq219582
       grind)
    | exact superpose eq219582 eq18
    | exact resolve eq18 eq219582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219582
  have eq220957 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (τ y) := by
    intro X0
    first
    | (have i₁ := eq76949 sF0 x
       have i₂ := eq218930 sF0
       grind)
    | exact superpose eq218930 eq76949
    | exact resolve eq76949 eq218930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220984 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x (σ y)) ∨ y = (τ y) := by
    intro X0 X1
    first
    | (have i₁ := eq257 X0 X1 sF4
       have i₂ := eq218930 sF4
       grind)
    | exact superpose eq218930 eq257
    | exact resolve eq257 eq218930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221280 : ∀ X1 : G, (M.op x X1) = (M.op x (σ y)) ∨ y = (τ y) := by
    intro X1
    first
    | exact superpose eq218930 eq220984
    | exact resolve eq220984 eq218930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220984
  have eq221293 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (τ y) := by
    intro X0
    first
    | (have i₁ := eq220957 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq220957
    | (have j0 := eq220957 X0
       grind)
    | exact resolve eq220957 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220957
  have eq221774 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X1) ∨ y = (τ y) := by
    intro X1
    first
    | exact superpose eq219193 eq221280
    | exact resolve eq221280 eq219193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221280
  have eq221786 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (τ y) := by
    intro X0
    first
    | exact superpose eq20 eq221293
    | (have j0 := eq221293 X0
       grind)
    | exact resolve eq221293 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221293
  have eq222165 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X1) ∨ y = (τ y) := by
    intro X1
    first
    | exact superpose eq26 eq221774
    | (have j0 := eq221774 X1
       grind)
    | exact resolve eq221774 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221774
  have eq222174 : x = (σ (M.op x y)) ∨ y = (τ y) := by
    first
    | exact superpose eq218930 eq221786
    | exact resolve eq221786 eq218930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218930 eq221786
  have eq222407 : y = (τ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq219370 eq222165
    | (have j1 := eq219370 (σ y)
       grind)
    | exact resolve eq222165 eq219370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219370 eq222165
  have eq222415 : y = (τ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq219193 eq222174
    | exact resolve eq222174 eq219193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219193 eq222174
  have eq222540 : y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq222407
       grind)
    | exact superpose eq222407 eq14
    | exact resolve eq14 eq222407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222407
  have eq222585 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq222540
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq222540
    | exact resolve eq222540 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222540
  have eq222589 : (σ (M.op x y)) ≠ (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq222585 eq27
    | exact resolve eq27 eq222585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222585
  have eq222776 : y = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq222415
       grind)
    | exact superpose eq222415 eq14
    | exact resolve eq14 eq222415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222415
  have eq222821 : y = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq222776
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq222776
    | exact resolve eq222776 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222776
  have eq222825 : y = (σ y) := by
    first
    | (have r₁ := eq222821
       have r₂ := eq222589
       grind)
    | exact resolve eq222821 eq222589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222589 eq222821
  have eq222826 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq222825
       grind)
    | exact superpose eq222825 eq18
    | exact resolve eq18 eq222825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq222827 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq222825
       grind)
    | exact superpose eq222825 eq24
    | exact resolve eq24 eq222825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq222829 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq222825
       grind)
    | exact superpose eq222825 eq40
    | exact resolve eq40 eq222825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq222883 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (M.op X1 (M.op x y)) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq76949 X1 X0
       have i₂ := eq222825
       grind)
    | exact superpose eq222825 eq76949
    | exact resolve eq76949 eq222825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76949
  have eq223005 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (σ y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq222827 eq455
    | exact resolve eq455 eq222827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq236670 : ∀ X0 : G, x = (k y y) ∨ (M.op X0 X0) = y ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq218878 X0
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq218878
    | (have j0 := eq218878 X0
       have j1 := eq11 y y
       grind)
    | exact resolve eq218878 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236684 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) = (M.op x X1) ∨ y = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq257 y X1 X0
       have i₂ := eq218878 X2
       grind)
    | exact superpose eq218878 eq257
    | (have j1 := eq218878 X2
       grind)
    | exact resolve eq257 eq218878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq236793 : ∀ X0 : G, x = (σ x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq76196 y
       have i₂ := eq218878 X0
       grind)
    | exact superpose eq218878 eq76196
    | (have j1 := eq218878 X0
       grind)
    | exact resolve eq76196 eq218878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76196
  have eq236799 : ∀ X0 : G, x = (τ x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq76540 y
       have i₂ := eq218878 X0
       grind)
    | exact superpose eq218878 eq76540
    | (have j1 := eq218878 X0
       grind)
    | exact resolve eq76540 eq218878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76540
  have eq236806 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op x X1)) ∨ y = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76948 y X1 X0
       have i₂ := eq218878 X2
       grind)
    | exact superpose eq218878 eq76948
    | (have j1 := eq218878 X2
       grind)
    | exact resolve eq76948 eq218878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76948
  have eq236814 : ∀ X0 X1 : G, (M.op X0 X0) = (τ x) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq77273 y X0
       have i₂ := eq218878 X1
       grind)
    | exact superpose eq218878 eq77273
    | (have j1 := eq218878 X1
       grind)
    | exact resolve eq77273 eq218878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77273 eq218878
  have eq236902 : ∀ X0 : G, x = (k y y) ∨ (M.op X0 X0) = y ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq236670 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236670
  have eq236987 : ∀ X0 X1 : G, (M.op X1 X1) = (σ y) ∨ (M.op X0 X0) = (τ x) := by
    intro X0 X1
    first
    | (have i₁ := eq236814 X0 X1
       have i₂ := eq222825
       grind)
    | exact superpose eq222825 eq236814
    | (have j0 := eq236814 X0 X1
       grind)
    | exact resolve eq236814 eq222825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236814
  have eq236995 : ∀ X0 X1 X2 : G, (σ y) = (M.op X2 X2) ∨ (M.op X0 X0) = (σ (M.op x X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq236806 X0 X1 X2
       have i₂ := eq222825
       grind)
    | exact superpose eq222825 eq236806
    | (have j0 := eq236806 X0 X1 X2
       grind)
    | exact resolve eq236806 eq222825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236806
  have eq237002 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ x = (τ x) := by
    intro X0
    first
    | (have i₁ := eq236799 X0
       have i₂ := eq222825
       grind)
    | exact superpose eq222825 eq236799
    | exact resolve eq236799 eq222825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236799
  have eq237008 : ∀ X0 : G, x = (σ x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq236793 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq236793
    | (have j0 := eq236793 X0
       grind)
    | exact resolve eq236793 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236793
  have eq237115 : ∀ X0 X1 X2 : G, (σ y) = (M.op X2 X2) ∨ (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) = (M.op x X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq236684 X0 X1 X2
       have i₂ := eq222825
       grind)
    | exact superpose eq222825 eq236684
    | (have j0 := eq236684 X0 X1 X2
       grind)
    | exact resolve eq236684 eq222825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236684
  have eq237129 : x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have j0 := eq236902 y
       have j1 := eq45023 x y y
       grind)
    | (have r₁ := eq236902 x
       have r₂ := eq45023 x y x
       grind)
    | (have r₁ := eq236902 x
       have r₂ := eq45023 y y x
       grind)
    | exact resolve eq236902 eq45023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45023 eq236902
  have eq237232 : ∀ X1 X2 : G, (σ y) = (M.op X2 X2) ∨ (σ (M.op x X1)) = (τ x) := by
    intro X1 X2
    first
    | exact superpose eq236987 eq236995
    | (have j0 := eq236995 x X1 X2
       have j1 := eq236987 x X2
       grind)
    | exact resolve eq236995 eq236987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236987 eq236995
  have eq237240 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq237008 X0
       have i₂ := eq222825
       grind)
    | exact superpose eq222825 eq237008
    | exact resolve eq237008 eq222825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237008
  have eq237329 : ∀ X1 X2 : G, (σ y) = (M.op X2 X2) ∨ (k (σ y) (σ y)) = (M.op x X1) := by
    intro X1 X2
    first
    | exact superpose eq2420 eq237115
    | (have j0 := eq237115 x X1 X2
       have j1 := eq2420 (σ y) X2 X2
       grind)
    | exact resolve eq237115 eq2420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420 eq237115
  have eq237339 : x = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq237129
       have i₂ := eq222825
       grind)
    | exact superpose eq222825 eq237129
    | exact resolve eq237129 eq222825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237129
  have eq237399 : ∀ X1 X2 : G, (σ y) = (M.op X2 X2) ∨ x = (σ (M.op x X1)) := by
    intro X1 X2
    first
    | exact superpose eq237002 eq237232
    | (have j0 := eq237232 X1 X2
       have j1 := eq237002 X2
       grind)
    | exact resolve eq237232 eq237002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237002 eq237232
  have eq237491 : ∀ X1 X2 : G, (σ y) = (M.op X2 X2) ∨ (k (σ y) (σ y)) = (M.op (σ x) X1) := by
    intro X1 X2
    first
    | exact superpose eq237240 eq237329
    | (have j0 := eq237329 X1 X2
       have j1 := eq237240 X2
       grind)
    | exact resolve eq237329 eq237240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237329
  have eq237499 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq237339
       have i₂ := eq222825
       grind)
    | exact superpose eq222825 eq237339
    | exact resolve eq237339 eq222825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237339
  have eq237546 : ∀ X1 X2 : G, (σ y) = (M.op X2 X2) ∨ (σ x) = (σ (M.op (σ x) X1)) := by
    intro X1 X2
    first
    | exact superpose eq237240 eq237399
    | (have j0 := eq237399 X1 X2
       have j1 := eq237240 X2
       grind)
    | exact resolve eq237399 eq237240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237399
  have eq237623 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq237240 eq237499
    | (have j1 := eq237240 (σ y)
       grind)
    | exact resolve eq237499 eq237240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237499
  have eq237662 : ∀ X2 : G, (σ y) = (M.op X2 X2) ∨ (σ x) = (σ (k (σ y) (σ y))) := by
    intro X2
    first
    | exact superpose eq237491 eq237546
    | (have j0 := eq237546 x X2
       have j1 := eq237491 x X2
       grind)
    | exact resolve eq237546 eq237491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237491 eq237546
  have eq237746 : ∀ X2 : G, (σ x) = (k (σ (σ y)) (σ y)) ∨ (σ y) = (M.op X2 X2) := by
    intro X2
    first
    | exact superpose eq222829 eq237662
    | (have j0 := eq237662 X2
       grind)
    | exact resolve eq237662 eq222829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222829 eq237662
  have eq237792 : ∀ X2 : G, (σ y) = (M.op X2 X2) ∨ (σ x) = (k (σ y) (σ y)) := by
    intro X2
    first
    | exact superpose eq222827 eq237746
    | (have j0 := eq237746 X2
       grind)
    | exact resolve eq237746 eq222827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237746
  have eq238509 : ∀ X1 : G, (k (σ y) X1) = (M.op X1 (σ y)) ∨ x = (σ x) := by
    intro X1
    first
    | (have i₁ := eq693 x (M.op x x) x
       have i₂ := eq237240 (M.op x x)
       grind)
    | exact superpose eq237240 eq693
    | exact resolve eq693 eq237240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq237240
  have eq255955 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op (σ y) X1)) ∨ (σ x) = (k (σ y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq237623 eq78251
    | exact resolve eq78251 eq237623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78251 eq237623
  have eq256058 : ∀ X1 : G, (σ y) = (τ (M.op (σ y) X1)) ∨ (σ x) = (k (σ y) (σ y)) := by
    intro X1
    first
    | exact superpose eq237792 eq255955
    | exact resolve eq255955 eq237792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237792 eq255955
  have eq261057 : (M.op x y) = (k (σ y) x) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq238509 eq219587
    | exact resolve eq219587 eq238509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219587
  have eq261061 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (σ x) := by
    first
    | exact superpose eq238509 eq26
    | (have j1 := eq238509 (σ x)
       grind)
    | exact resolve eq26 eq238509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238509
  have eq261069 : (M.op x y) = (k (σ y) x) ∨ x = (σ x) := by grind
  clear eq261057
  have eq263183 : (τ (M.op (σ x) (σ y))) = (k (σ y) (τ (σ x))) ∨ x = (σ x) := by
    first
    | exact superpose eq261061 eq223005
    | exact resolve eq223005 eq261061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223005 eq261061
  have eq263190 : (τ (M.op (σ x) (σ y))) = (k (σ y) x) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq263183
    | exact resolve eq263183 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq263183
  have eq263196 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    first
    | exact superpose eq261069 eq263190
    | exact resolve eq263190 eq261069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261069 eq263190
  have eq263203 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq263196 eq14
    | exact resolve eq14 eq263196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263196
  have eq263256 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq263203
    | exact resolve eq263203 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263203
  have eq263259 : x = (σ x) := by
    first
    | (have r₁ := eq263256
       have r₂ := eq27
       grind)
    | exact resolve eq263256 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263256
  have eq263263 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq22
       have i₂ := eq263259
       grind)
    | exact superpose eq263259 eq22
    | exact resolve eq22 eq263259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq263265 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq263259
       grind)
    | exact superpose eq263259 eq39
    | exact resolve eq39 eq263259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq263292 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq222826
       have i₂ := eq263259
       grind)
    | exact superpose eq263259 eq222826
    | exact resolve eq222826 eq263259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222826 eq263259
  have eq263316 : (σ x) = (τ (σ x)) := by
    first
    | exact superpose eq263263 eq15
    | exact resolve eq15 eq263263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263263
  have eq263669 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq263292 eq26
    | exact resolve eq26 eq263292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267285 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq263669 eq27
    | exact resolve eq27 eq263669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq275645 : ∀ X0 X2 : G, (k (σ y) (σ y)) = (σ (M.op (M.op X0 (M.op x y)) (σ y))) ∨ y = (τ (M.op (σ y) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq48174 X2 x
       have i₂ := eq222883 x X0
       grind)
    | exact superpose eq222883 eq48174
    | (have j0 := eq48174 X2 X2
       grind)
    | exact resolve eq48174 eq222883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275807 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (σ (M.op (M.op X0 (M.op x y)) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq214232 x
       have i₂ := eq222883 x X0
       grind)
    | exact superpose eq222883 eq214232
    | exact resolve eq214232 eq222883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214232 eq222883
  have eq276270 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (σ (M.op (M.op X0 (M.op x y)) (σ y))) := by
    intro X0
    first
    | (have j0 := eq275807 X0
       grind)
    | (have r₁ := eq275807 X0
       have r₂ := eq267285
       grind)
    | exact resolve eq275807 eq267285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275807
  have eq276329 : ∀ X0 X2 : G, (σ y) = (τ (M.op (σ y) X2)) ∨ (k (σ y) (σ y)) = (σ (M.op (M.op X0 (M.op x y)) (σ y))) := by
    intro X0 X2
    first
    | (have i₁ := eq275645 X0 X2
       have i₂ := eq222825
       grind)
    | exact superpose eq222825 eq275645
    | (have j0 := eq275645 X0 X2
       grind)
    | exact resolve eq275645 eq222825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275645
  have eq276588 : ∀ X2 : G, (k (σ y) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (τ (M.op (σ y) X2)) := by
    intro X2
    first
    | exact superpose eq276270 eq276329
    | (have j0 := eq276329 x X2
       grind)
    | exact resolve eq276329 eq276270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276329
  have eq276728 : ∀ X2 : G, (σ x) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (τ (M.op (σ y) X2)) := by
    intro X2
    first
    | exact superpose eq256058 eq276588
    | (have j0 := eq276588 X2
       have j1 := eq256058 X2
       grind)
    | exact resolve eq276588 eq256058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276588
  have eq292570 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (σ (M.op (k (σ y) (σ y)) (σ y))) ∨ y = (τ (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq276270 sF0
       have i₂ := eq48174 x sF0
       grind)
    | exact superpose eq48174 eq276270
    | (have j1 := eq48174 X0 x
       grind)
    | exact resolve eq276270 eq48174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48174 eq276270
  have eq293080 : ∀ X0 : G, (σ y) = (τ (M.op (σ y) X0)) ∨ (k (M.op x y) (M.op x y)) = (σ (M.op (k (σ y) (σ y)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq292570 X0
       have i₂ := eq222825
       grind)
    | exact superpose eq222825 eq292570
    | exact resolve eq292570 eq222825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222825 eq292570
  have eq293286 : ∀ X0 : G, (σ y) = (τ (M.op (σ y) X0)) ∨ (k (M.op x y) (M.op x y)) = (σ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq256058 eq293080
    | (have j0 := eq293080 X0
       have j1 := eq256058 X0
       grind)
    | exact resolve eq293080 eq256058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256058 eq293080
  have eq293424 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (τ (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq293286
    | (have j0 := eq293286 X0
       grind)
    | exact resolve eq293286 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq293286
  have eq293478 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (τ (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq263669 eq293424
    | (have j0 := eq293424 X0
       grind)
    | exact resolve eq293424 eq263669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263669 eq293424
  have eq293488 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (τ (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq20 eq293478
    | (have j0 := eq293478 X0
       grind)
    | exact resolve eq293478 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293478
  have eq293492 : ∀ X0 : G, (σ y) = (τ (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq276728 eq293488
    | (have j0 := eq293488 X0
       have j1 := eq276728 X0
       grind)
    | exact resolve eq293488 eq276728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276728 eq293488
  have eq293556 : ∀ X0 : G, (M.op (σ y) X0) = (σ (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq293492 eq14
    | exact resolve eq14 eq293492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293492
  have eq293617 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq222827 eq293556
    | exact resolve eq293556 eq222827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293556
  have eq293779 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq293617 eq695
    | exact resolve eq695 eq293617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq293617
  have eq331170 : (M.op x y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq293779 eq263292
    | exact resolve eq263292 eq293779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263292 eq293779
  have eq333687 : (σ (M.op x y)) = (k (σ (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq331170 eq263265
    | exact resolve eq263265 eq331170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263265
  have eq333691 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq222827 eq333687
    | exact resolve eq333687 eq222827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222827 eq333687
  have eq333703 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq333691
    | exact resolve eq333691 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq333691
  have eq333713 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq331170 eq333703
    | exact resolve eq333703 eq331170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331170 eq333703
  have eq333722 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq333713
       have r₂ := eq267285
       grind)
    | exact resolve eq333713 eq267285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333713
  have eq333725 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq333722 eq28
    | exact resolve eq28 eq333722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq333781 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq333722 eq267285
    | exact resolve eq267285 eq333722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267285 eq333722
  have eq333941 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq333725 eq263316
    | exact resolve eq263316 eq333725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263316 eq333725
  have eq334012 : False := by grind
  exact eq334012
