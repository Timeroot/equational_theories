import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq267 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq267 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq267 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq279 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq268 (σ X0)
       grind)
    | exact superpose eq268 eq15
    | exact resolve eq15 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq268 (τ X0)
       grind)
    | exact superpose eq268 eq31
    | exact resolve eq31 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq292 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq285 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq285
    | exact resolve eq285 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq279
    | exact resolve eq279 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq279
  have eq411 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq428 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq411 X0 X1
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq411
    | (have j0 := eq411 X0 X1
       grind)
    | exact resolve eq411 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq820 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq428 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq428
    | exact resolve eq428 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq859 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq820 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq820
    | (have j0 := eq820 X0 X1
       grind)
    | exact resolve eq820 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq820
  have eq862 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq859 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq859 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq859 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq863 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq862 X0 X1
       have i₂ := eq292 X0
       grind)
    | exact superpose eq292 eq862
    | (have j0 := eq862 X0 X1
       grind)
    | exact resolve eq862 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292 eq862
  have eq864 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq863 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq863
    | (have j0 := eq863 X0 X1
       grind)
    | exact resolve eq863 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq865 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq864 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq864
    | exact resolve eq864 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq876 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq864 (σ X0) X1
       grind)
    | exact superpose eq864 eq15
    | (have j1 := eq864 (σ X0) X1
       grind)
    | exact resolve eq15 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq908 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq876 X0 X1
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq876
    | (have j0 := eq876 X0 X1
       grind)
    | exact resolve eq876 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq946 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq865 (τ X1) X0
       grind)
    | exact superpose eq865 eq17
    | (have j1 := eq865 (τ X1) X0
       grind)
    | exact resolve eq17 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq865
  have eq1124 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq946 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq946
    | exact resolve eq946 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq1172 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1124 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1124
    | (have j0 := eq1124 X0 X1
       grind)
    | exact resolve eq1124 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq2385 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq908 x y
       grind)
    | exact superpose eq908 eq16
    | (have j1 := eq908 x y
       grind)
    | exact resolve eq16 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2399 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq908 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq2426 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2385
       have i₂ := eq1172 y x
       grind)
    | exact superpose eq1172 eq2385
    | (have j1 := eq1172 y x
       grind)
    | (have r₁ := eq2385
       have r₂ := eq1172 y x
       grind)
    | exact resolve eq2385 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2385
  have eq2427 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2426
  have eq2432 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2427
       grind)
    | exact superpose eq2427 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2427
       grind)
    | exact resolve eq13 eq2427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2434 : x ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2427
       grind)
    | exact superpose eq2427 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq2427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2427
  have eq2436 : x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2432
  have eq2437 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2436
       have r₂ := eq2434
       grind)
    | exact resolve eq2436 eq2434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2434 eq2436
  have eq2462 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2399 x y
       have i₂ := eq2437
       grind)
    | exact superpose eq2437 eq2399
    | (have j0 := eq2399 x y
       grind)
    | exact resolve eq2399 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399 eq2437
  have eq2485 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2462
  have eq2486 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2485
  have eq2570 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2486
       grind)
    | exact superpose eq2486 eq16
    | exact resolve eq16 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2574 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2486
       grind)
    | exact superpose eq2486 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2576 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2486
       grind)
    | exact superpose eq2486 eq12
    | exact resolve eq12 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486
  have eq2578 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2576
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2576
    | exact resolve eq2576 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2576
  have eq2579 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2574
       have r₂ := eq298 x
       grind)
    | exact resolve eq2574 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574
  have eq2580 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2579
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2579
    | exact resolve eq2579 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579
  have eq2581 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2580
       have i₂ := eq298 x
       grind)
    | exact superpose eq298 eq2580
    | exact resolve eq2580 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq2580
  have eq2582 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2581
       have r₂ := eq2578
       grind)
    | exact resolve eq2581 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578 eq2581
  have eq2590 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1172 y x
       have i₂ := eq2582
       grind)
    | exact superpose eq2582 eq1172
    | (have j0 := eq1172 y x
       grind)
    | exact resolve eq1172 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172 eq2582
  have eq2637 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2590
       have r₂ := eq2570
       grind)
    | exact resolve eq2590 eq2570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590
  have eq2654 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2570
       have i₂ := eq2637
       grind)
    | exact superpose eq2637 eq2570
    | exact resolve eq2570 eq2637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570 eq2637
  have eq2662 : False := by grind
  exact eq2662

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq320 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq320
  have eq327 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq340 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq327 (σ X0)
       grind)
    | exact superpose eq327 eq15
    | exact resolve eq15 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq327 (τ X0)
       grind)
    | exact superpose eq327 eq32
    | exact resolve eq32 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq346 X0
       have i₂ := eq327 X0
       grind)
    | exact superpose eq327 eq346
    | exact resolve eq346 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq359 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq340 X0
       have i₂ := eq327 X0
       grind)
    | exact superpose eq327 eq340
    | exact resolve eq340 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq340
  have eq408 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq13
    | exact resolve eq13 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq411 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq409 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq409
    | exact resolve eq409 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq417 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq411
  have eq644 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq652 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq661 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq644 X0 X1
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq644
    | (have j0 := eq644 X0 X1
       grind)
    | exact resolve eq644 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq675 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq661 X0 X1
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq661
    | (have j0 := eq661 X0 X1
       grind)
    | exact resolve eq661 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq661
  have eq700 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq675 x y
       grind)
    | exact superpose eq675 eq16
    | (have j1 := eq675 x y
       grind)
    | exact resolve eq16 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq675 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq3843 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq652
    | exact resolve eq652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq3919 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3843 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3843
    | (have j0 := eq3843 X0 X1
       grind)
    | exact resolve eq3843 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843
  have eq10786 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq700
       have i₂ := eq3919 y x
       grind)
    | exact superpose eq3919 eq700
    | (have j1 := eq3919 y x
       grind)
    | (have r₁ := eq700
       have r₂ := eq3919 y x
       grind)
    | exact resolve eq700 eq3919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700 eq3919
  have eq10787 : (M.op x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq10786
  have eq17534 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq713 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq713
    | (have j0 := eq713 (τ X1) (τ X0)
       grind)
    | exact resolve eq713 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq17611 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X1 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17534 X0 X1
       have i₂ := eq353 X1
       grind)
    | exact superpose eq353 eq17534
    | (have j0 := eq17534 X0 X1
       grind)
    | exact resolve eq17534 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17534
  have eq17651 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17611 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq17611
    | (have j0 := eq17611 X0 X1
       grind)
    | exact resolve eq17611 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17611
  have eq17690 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17651 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq17651
    | (have j0 := eq17651 X0 X1
       grind)
    | exact resolve eq17651 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17651
  have eq17722 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17690 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17690
    | (have j0 := eq17690 X0 X1
       grind)
    | exact resolve eq17690 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17690
  have eq17745 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17722 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq17722
    | (have j0 := eq17722 X0 X1
       grind)
    | exact resolve eq17722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17722
  have eq17767 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17745 X0 X1
       have i₂ := eq353 X1
       grind)
    | exact superpose eq353 eq17745
    | (have j0 := eq17745 X0 X1
       grind)
    | exact resolve eq17745 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17745
  have eq17785 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17767 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq17767
    | (have j0 := eq17767 X0 X1
       grind)
    | exact resolve eq17767 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17767
  have eq17802 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17785 X0 X1
       have i₂ := eq353 X1
       grind)
    | exact superpose eq353 eq17785
    | (have j0 := eq17785 X0 X1
       grind)
    | exact resolve eq17785 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq17785
  have eq17814 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17802 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq17802
    | (have j0 := eq17802 X0 X1
       grind)
    | exact resolve eq17802 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17802
  have eq17825 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17814 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17814
    | (have j0 := eq17814 X0 X1
       grind)
    | exact resolve eq17814 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17814
  have eq56459 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq10787
       grind)
    | exact superpose eq10787 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10787
       grind)
    | exact resolve eq13 eq10787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10787
  have eq56464 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq56459
  have eq56465 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq56464
  have eq69120 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq408 x (σ y)
       have i₂ := eq56465
       grind)
    | exact superpose eq56465 eq408
    | (have j0 := eq408 x (σ y)
       grind)
    | (have r₁ := eq408 x (σ y)
       have r₂ := eq56465
       grind)
    | exact resolve eq408 eq56465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56465
  have eq69138 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq69120
  have eq69139 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq69138
  have eq69142 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq69139
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq69139
    | exact resolve eq69139 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69139
  have eq69157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq417 x
       have i₂ := eq69142
       grind)
    | exact superpose eq69142 eq417
    | exact resolve eq417 eq69142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69142
  have eq69189 : (k y x) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq69157
       have r₂ := eq16
       grind)
    | exact resolve eq69157 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69157
  have eq69196 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq713 x y
       have i₂ := eq69189
       grind)
    | exact superpose eq69189 eq713
    | (have j0 := eq713 x y
       grind)
    | (have r₁ := eq713 x y
       have r₂ := eq69189
       grind)
    | exact resolve eq713 eq69189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69189
  have eq69254 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq69196
  have eq69255 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq69254
  have eq69261 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have j1 := eq713 x y
       grind)
    | (have r₁ := eq69255
       have r₂ := eq713 x y
       grind)
    | exact resolve eq69255 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq69255
  have eq69266 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69261
       grind)
    | exact superpose eq69261 eq16
    | exact resolve eq16 eq69261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69267 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq408 x (σ y)
       have i₂ := eq69261
       grind)
    | exact superpose eq69261 eq408
    | (have j0 := eq408 x (σ y)
       grind)
    | (have r₁ := eq408 x (σ y)
       have r₂ := eq69261
       grind)
    | exact resolve eq408 eq69261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408 eq69261
  have eq69285 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq69267
  have eq69286 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq69285
  have eq69289 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq69286
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq69286
    | exact resolve eq69286 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69286
  have eq69310 : (k y x) = (τ (σ (M.op x x))) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq69289
       grind)
    | exact superpose eq69289 eq10
    | exact resolve eq10 eq69289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69289
  have eq69519 : (k y x) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq69310
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq69310
    | exact resolve eq69310 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69310
  have eq69571 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17825 y x
       have i₂ := eq69519
       grind)
    | exact superpose eq69519 eq17825
    | (have j0 := eq17825 y x
       grind)
    | (have r₁ := eq17825 y x
       have r₂ := eq69519
       grind)
    | exact resolve eq17825 eq69519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17825 eq69519
  have eq69589 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq69571
  have eq69597 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq69266
       have i₂ := eq69589
       grind)
    | exact superpose eq69589 eq69266
    | exact resolve eq69266 eq69589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69266 eq69589
  have eq69609 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq69597
  have eq69610 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq69609
  have eq69618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq417 x
       have i₂ := eq69610
       grind)
    | exact superpose eq69610 eq417
    | exact resolve eq417 eq69610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69610
  have eq69650 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq69618
       have r₂ := eq16
       grind)
    | exact resolve eq69618 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69618
  have eq69666 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq69650
       grind)
    | exact superpose eq69650 eq10
    | exact resolve eq10 eq69650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69650
  have eq69870 : y = (M.op x x) := by
    first
    | (have i₁ := eq69666
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq69666
    | exact resolve eq69666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69666
  have eq69900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq417 x
       have i₂ := eq69870
       grind)
    | exact superpose eq69870 eq417
    | exact resolve eq417 eq69870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq69870
  have eq69933 : False := by grind
  exact eq69933

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq54 (τ X0)
       grind)
    | exact superpose eq54 eq18
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq62 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq62
    | exact resolve eq62 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq62
  have eq79 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq90
  have eq177 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | (have j0 := eq92 X1 X1
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq194 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq177
    | (have j0 := eq177 X0 X1
       grind)
    | exact resolve eq177 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq177
  have eq200 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq194 X0 X1
       have j1 := eq79 X1 X0
       grind)
    | (have r₁ := eq194 X0 X0
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq194 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq194
  have eq204 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq200
    | (have j0 := eq200 X0 X1
       grind)
    | exact resolve eq200 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq200
  have eq364 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq204
    | exact resolve eq204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq409 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq364 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq364 X0 X1
       grind)
    | exact superpose eq364 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq364 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq364 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq364 X0 X1
       grind)
    | exact resolve eq13 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq409 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq423 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq419 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq419 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq419 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq465 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq423 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq469 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq465 X0 X1
       have j1 := eq364 X1 X0
       grind)
    | (have r₁ := eq465 X0 X0
       have r₂ := eq364 X0 X0
       grind)
    | (have r₁ := eq465 X1 X0
       have r₂ := eq364 X0 X1
       grind)
    | exact resolve eq465 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq465
  have eq578 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq469 (σ X1) (σ X0)
       grind)
    | exact superpose eq469 eq15
    | exact resolve eq15 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 X1
       have i₂ := eq469 X1 X0
       grind)
    | exact superpose eq469 eq578
    | exact resolve eq578 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq578
  have eq991 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq597 x y
       grind)
    | exact superpose eq597 eq16
    | (have r₁ := eq16
       have r₂ := eq597 x y
       grind)
    | exact resolve eq16 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq1005 : False := by grind
  exact eq1005

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  clear eq55 eq57
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
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq86
  have eq251 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq263 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq251 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq268 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq263 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq263 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq263 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq280 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       have j1 := eq80 X0 (σ X1)
       grind)
    | (have r₁ := eq268 X0 X1
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq268 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq268
  have eq287 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq280
    | (have j0 := eq280 X0 X1
       grind)
    | exact resolve eq280 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq288 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq287 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq292 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq288 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq288
    | exact resolve eq288 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq288 x y
       grind)
    | exact superpose eq288 eq16
    | exact resolve eq16 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq369 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq292 X0 (τ X1)
       grind)
    | exact superpose eq292 eq17
    | exact resolve eq17 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq292
  have eq395 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq369 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq369
    | exact resolve eq369 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq408 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq395 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq395
    | exact resolve eq395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq437 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq303
       have i₂ := eq408 x y
       grind)
    | exact superpose eq408 eq303
    | exact resolve eq303 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303 eq408
  have eq438 : False := by grind
  exact eq438

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq76 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq121 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq71 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq71 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq71 X0 X1
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq125 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq121 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq127 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq125 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq125 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq125 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq3862 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq72 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq3863 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq3862 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3862
  have eq3866 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3863 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3863
    | (have j0 := eq3863 X0
       grind)
    | exact resolve eq3863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3863
  have eq3870 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3866 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3866
    | exact resolve eq3866 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3866
  have eq3909 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3870 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq3870
    | (have j0 := eq3870 X0
       grind)
    | exact resolve eq3870 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3870
  have eq3911 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq3909 X0
       grind)
    | exact superpose eq3909 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq3909 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3909 X0
       grind)
    | exact resolve eq12 eq3909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3909
  have eq3933 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3911 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3911
  have eq3946 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq76
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq3987 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3946 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq3946
    | (have j0 := eq3946 X0 X0
       grind)
    | exact resolve eq3946 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3946
  have eq4004 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3933 X0 X1
       grind)
    | exact superpose eq3933 eq11
    | (have j1 := eq3933 X0 X1
       grind)
    | exact resolve eq11 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3933
  have eq4095 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4004 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4004
    | (have j0 := eq4004 X0 X0
       grind)
    | exact resolve eq4004 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4004
  have eq4176 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4095 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4095
  have eq4177 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4176 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4176
  have eq4328 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq4177 X0
       grind)
    | exact superpose eq4177 eq127
    | (have j0 := eq127 X0 X1
       grind)
    | exact resolve eq127 eq4177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq4337 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq122 X0 X0
       have i₂ := eq4177 X0
       grind)
    | exact superpose eq4177 eq122
    | (have j0 := eq122 X0 X0
       grind)
    | exact resolve eq122 eq4177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq4361 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4177 (σ X0)
       grind)
    | exact superpose eq4177 eq15
    | exact resolve eq15 eq4177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4394 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4337 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4337
  have eq4426 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4361 X0
       have i₂ := eq4177 X0
       grind)
    | exact superpose eq4177 eq4361
    | exact resolve eq4361 eq4177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4177 eq4361
  have eq6742 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X2 X0)) = (τ (M.op X0 X2)) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq3987 X0 X2
       grind)
    | exact superpose eq3987 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq3987 X0 X2
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3987 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq3987 X1 X1
       grind)
    | exact resolve eq12 eq3987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3987
  have eq6785 : ∀ X0 X1 X2 : G, (τ (k X2 X0)) = (τ (M.op X0 X2)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq6742 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6742
  have eq14803 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq6785 X0 X2 X1
       grind)
    | exact superpose eq6785 eq11
    | (have j1 := eq6785 X0 X2 X1
       grind)
    | exact resolve eq11 eq6785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6785
  have eq14932 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14803 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq14803
    | (have j0 := eq14803 X0 X1 X1
       grind)
    | exact resolve eq14803 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14803
  have eq15291 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14932 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14932
  have eq15292 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15291 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15291
  have eq15448 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq15292 X1 (τ X0)
       grind)
    | exact superpose eq15292 eq18
    | (have j1 := eq15292 X1 (τ X0)
       grind)
    | exact resolve eq18 eq15292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq15488 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq15292 (σ X1) (σ X0)
       grind)
    | exact superpose eq15292 eq15
    | (have j1 := eq15292 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq15292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15292
  have eq17322 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15448 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15448
    | exact resolve eq15448 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15448
  have eq17453 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17322 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq17322
    | (have j0 := eq17322 X0 X1
       grind)
    | exact resolve eq17322 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17322
  have eq19539 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15488 x y
       grind)
    | exact superpose eq15488 eq16
    | (have j1 := eq15488 x y
       grind)
    | exact resolve eq16 eq15488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19621 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq15488 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15488
  have eq19755 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19621 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq19621
    | (have j0 := eq19621 (τ X1) (τ X0)
       grind)
    | exact resolve eq19621 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq19831 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19755 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq19755
    | (have j0 := eq19755 X0 X1
       grind)
    | exact resolve eq19755 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19755
  have eq19868 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19831 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19831
    | (have j0 := eq19831 X0 X1
       grind)
    | exact resolve eq19831 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19831
  have eq19887 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19868 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19868
    | (have j0 := eq19868 X0 X1
       grind)
    | exact resolve eq19868 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19868
  have eq19901 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19887 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq19887
    | (have j0 := eq19887 X0 X1
       grind)
    | exact resolve eq19887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19887
  have eq20810 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19539
       have i₂ := eq17453 x y
       grind)
    | exact superpose eq17453 eq19539
    | (have j1 := eq17453 (σ x) (σ y)
       grind)
    | (have r₁ := eq19539
       have r₂ := eq17453 x y
       grind)
    | exact resolve eq19539 eq17453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17453 eq19539
  have eq20813 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20810
  have eq20818 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq20813
       grind)
    | exact superpose eq20813 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20813
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20813
       grind)
    | exact resolve eq13 eq20813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20813
  have eq20841 : y = (k y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20818
  have eq28527 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19621 x y
       have i₂ := eq20841
       grind)
    | exact superpose eq20841 eq19621
    | (have j0 := eq19621 x y
       grind)
    | exact resolve eq19621 eq20841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19621 eq20841
  have eq28534 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq28527
  have eq28535 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq28534
  have eq28556 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28535
       grind)
    | exact superpose eq28535 eq16
    | exact resolve eq16 eq28535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28564 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq28535
       grind)
    | exact superpose eq28535 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq28535
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq28535
       grind)
    | exact resolve eq13 eq28535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28535
  have eq28593 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq28564
  have eq28597 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28593
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq28593
    | exact resolve eq28593 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28593
  have eq28600 : x = (M.op x x) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq28597
       have i₂ := eq4426 x
       grind)
    | exact superpose eq4426 eq28597
    | exact resolve eq28597 eq4426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28597
  have eq36785 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4394 x
       have i₂ := eq28600
       grind)
    | exact superpose eq28600 eq4394
    | (have j0 := eq4394 x
       grind)
    | (have r₁ := eq4394 x
       have r₂ := eq28600
       grind)
    | exact resolve eq4394 eq28600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28600
  have eq36843 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq36785
  have eq36872 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have j1 := eq4394 x
       grind)
    | (have r₁ := eq36843
       have r₂ := eq4394 x
       grind)
    | exact resolve eq36843 eq4394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36843
  have eq36884 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq36872
       have i₂ := eq4426 x
       grind)
    | exact superpose eq4426 eq36872
    | exact resolve eq36872 eq4426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36872
  have eq36901 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq36884
       grind)
    | exact superpose eq36884 eq10
    | exact resolve eq10 eq36884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36884
  have eq37064 : y = (k y x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq36901
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq36901
    | exact resolve eq36901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36901
  have eq37301 : y ≠ y ∨ y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq19901 y x
       have i₂ := eq37064
       grind)
    | exact superpose eq37064 eq19901
    | (have j0 := eq19901 y x
       grind)
    | (have r₁ := eq19901 y x
       have r₂ := eq37064
       grind)
    | exact resolve eq19901 eq37064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19901 eq37064
  have eq37310 : y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq37301
  have eq37323 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq28556
       have i₂ := eq37310
       grind)
    | exact superpose eq37310 eq28556
    | exact resolve eq28556 eq37310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28556 eq37310
  have eq37359 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq37323
  have eq37616 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq4328 x X0
       have i₂ := eq37359
       grind)
    | exact superpose eq37359 eq4328
    | (have j0 := eq4328 x X0
       grind)
    | (have r₁ := eq4328 x x
       have r₂ := eq37359
       grind)
    | exact resolve eq4328 eq37359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37621 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4394 x
       have i₂ := eq37359
       grind)
    | exact superpose eq37359 eq4394
    | (have j0 := eq4394 x
       grind)
    | (have r₁ := eq4394 x
       have r₂ := eq37359
       grind)
    | exact resolve eq4394 eq37359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37359
  have eq37679 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq37621
  have eq37684 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq37616 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37616
  have eq37708 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq4394 x
       grind)
    | (have r₁ := eq37679
       have r₂ := eq4394 x
       grind)
    | exact resolve eq37679 eq4394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4394 eq37679
  have eq37711 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq37684 X0
       have j1 := eq4328 x X0
       grind)
    | (have r₁ := eq37684 X0
       have r₂ := eq4328 x x
       grind)
    | exact resolve eq37684 eq4328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4328 eq37684
  have eq37720 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq37708
       have i₂ := eq4426 x
       grind)
    | exact superpose eq4426 eq37708
    | exact resolve eq37708 eq4426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4426 eq37708
  have eq37739 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq37720
       grind)
    | exact superpose eq37720 eq10
    | exact resolve eq10 eq37720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37720
  have eq37911 : x = (M.op x x) := by
    first
    | (have i₁ := eq37739
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq37739
    | exact resolve eq37739 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37739
  have eq38405 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq37911
       grind)
    | exact superpose eq37911 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq37911
       grind)
    | exact resolve eq12 eq37911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37911
  have eq38477 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq38405 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38405
  have eq39344 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq37711 (σ X0)
       grind)
    | exact superpose eq37711 eq15
    | exact resolve eq15 eq37711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37711
  have eq39445 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq39344 X0
       have i₂ := eq38477 X0
       grind)
    | exact superpose eq38477 eq39344
    | exact resolve eq39344 eq38477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38477 eq39344
  have eq40019 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39445 y
       grind)
    | exact superpose eq39445 eq16
    | (have r₁ := eq16
       have r₂ := eq39445 y
       grind)
    | exact resolve eq16 eq39445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39445
  have eq40144 : False := by grind
  exact eq40144

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation3112 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X1 X0) X1) X0) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq36 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (σ X0) = (M.op (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq97 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq98 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq68 X1
       grind)
    | exact superpose eq68 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq100 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq195 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq195 X0 X1 X2
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq195
    | (have j0 := eq195 X0 X1 X2
       grind)
    | exact resolve eq195 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq195
  have eq381 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (M.op (σ (k X0 (M.op X0 X0))) (σ X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq100 (M.op X0 X0) X0
       grind)
    | exact superpose eq100 eq46
    | (have j1 := eq100 (M.op X0 X0) X0
       grind)
    | exact resolve eq46 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq100
  have eq1668 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op (M.op X1 (τ X0)) X1) (τ X0)))) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (M.op (M.op X1 (τ X0)) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 (M.op (M.op (M.op X1 (τ X1)) X1) (τ X1)) X1
       have i₂ := eq9 (τ X1) X1
       grind)
    | exact superpose eq9 eq98
    | (have j0 := eq98 (τ (M.op X0 X0)) X0
       grind)
    | exact resolve eq98 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1704 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (M.op X1 (τ X0)) X1) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op (M.op (M.op X1 (τ X0)) X1) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1668 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1668
    | (have j0 := eq1668 X0 X1
       grind)
    | exact resolve eq1668 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq4723 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op X3 (k (σ X1) X2)) ∨ (k (k (σ X1) X2) X3) = (M.op (σ X0) (k (σ X1) X2)) ∨ (k (σ X1) X2) = X3 ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k (σ X0) X1) X1
       have i₂ := eq205 X0 X1 X2
       grind)
    | exact superpose eq205 eq13
    | (have j0 := eq13 (k (k (σ X1) X2) X3) (M.op (σ X0) (k (σ X1) X2))
       have j1 := eq205 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq205 X0 X1 X2
       grind)
    | exact resolve eq13 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq64086 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op (M.op (M.op X1 (τ X0)) X1) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq1704 X0 X1
       grind)
    | exact superpose eq1704 eq9
    | (have j1 := eq1704 X0 X1
       grind)
    | exact resolve eq9 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704
  have eq64120 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op (M.op (M.op X1 (τ X0)) X1) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64086 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq64086
    | (have j0 := eq64086 X0 X1
       grind)
    | exact resolve eq64086 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64086
  have eq64121 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op (M.op (M.op X1 (τ X0)) X1) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq64120 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64120
  have eq64240 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (k X0 (σ (M.op (M.op (M.op X1 (τ X0)) X1) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq64121 X0 X1
       grind)
    | exact superpose eq64121 eq11
    | (have j1 := eq64121 X0 X1
       grind)
    | exact resolve eq11 eq64121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64121
  have eq64479 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ (M.op (M.op (M.op X1 (τ X0)) X1) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64240 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64240
    | (have j0 := eq64240 X0 X1
       grind)
    | exact resolve eq64240 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64240
  have eq65616 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ (M.op (M.op (M.op X1 (τ (σ X0))) X1) (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0
       have i₂ := eq64479 (σ X0) X1
       grind)
    | exact superpose eq64479 eq22
    | (have j1 := eq64479 (σ X0) X1
       grind)
    | exact resolve eq22 eq64479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64479
  have eq65687 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op (M.op (M.op X1 (τ (σ X0))) X1) (τ (σ X0))))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65616 X0 X1
       have i₂ := eq15 X0 (M.op (M.op (M.op X1 (τ (σ X0))) X1) (τ (σ X0)))
       grind)
    | exact superpose eq15 eq65616
    | (have j0 := eq65616 X0 X1
       grind)
    | exact resolve eq65616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65616
  have eq65711 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op (M.op (M.op X1 X0) X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq65687 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65687
    | (have j0 := eq65687 X0 X1
       grind)
    | exact resolve eq65687 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65687
  have eq65785 : ∀ X0 X1 X2 : G, (τ (k X1 (σ X0))) = (k (τ X1) (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op (M.op (M.op X2 X0) X2) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 (M.op X0 X0)
       have i₂ := eq65711 X0 X2
       grind)
    | exact superpose eq65711 eq28
    | (have j1 := eq65711 X0 X2
       grind)
    | exact resolve eq28 eq65711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65711
  have eq65974 : ∀ X0 X1 X2 : G, (k (τ X1) X0) = (k (τ X1) (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op (M.op (M.op X2 X0) X2) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65785 X0 X1 X2
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq65785
    | (have j0 := eq65785 X0 X1 X2
       grind)
    | exact resolve eq65785 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq65785
  have eq66052 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (M.op (τ X0) (τ X0))) X0) ∨ (M.op (M.op (σ (k (τ X0) (M.op (τ X0) (τ X0)))) X0) X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq381 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq381
    | exact resolve eq381 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq66196 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op (M.op (σ (k (τ X0) (M.op (τ X0) (τ X0)))) X0) X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq66052 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq66052
    | (have j0 := eq66052 X0
       grind)
    | exact resolve eq66052 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66052
  have eq66245 : ∀ X0 : G, (M.op (M.op (k X0 (σ (M.op (τ X0) (τ X0)))) X0) X0) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq66196 X0
       have i₂ := eq18 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq18 eq66196
    | (have j0 := eq66196 X0
       grind)
    | exact resolve eq66196 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66196
  have eq66265 : ∀ X0 : G, (M.op (M.op (k X0 (M.op X0 X0)) X0) X0) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq66245 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq66245
    | (have j0 := eq66245 X0
       grind)
    | exact resolve eq66245 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66245
  have eq66280 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op (M.op (k X0 (M.op X0 X0)) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq66265 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq66265
    | (have j0 := eq66265 X0
       grind)
    | exact resolve eq66265 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66265
  have eq69990 : ∀ X0 X1 X2 : G, (σ X1) = (σ (k X1 (M.op (M.op (M.op X2 X1) X2) X1))) ∨ (k X0 X1) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65974 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65974
    | (have j0 := eq65974 X1 X1 X2
       grind)
    | exact resolve eq65974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65974
  have eq71052 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (M.op (M.op (M.op X1 X0) X1) X0)) ∨ (k X2 X0) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X0 (M.op (M.op (M.op X1 X0) X1) X0))
       have i₂ := eq69990 X2 X0 X1
       grind)
    | exact superpose eq69990 eq10
    | (have j1 := eq69990 X2 X0 X2
       grind)
    | exact resolve eq10 eq69990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69990
  have eq71259 : ∀ X0 X1 X2 : G, (k X2 X0) = (k X2 (M.op X0 X0)) ∨ (k X0 (M.op (M.op (M.op X1 X0) X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71052 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71052
    | (have j0 := eq71052 X0 X1 X2
       grind)
    | exact resolve eq71052 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71052
  have eq91203 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 ∨ (M.op (M.op (k X0 (M.op X0 X0)) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq66280 X0
       grind)
    | exact superpose eq66280 eq9
    | (have j1 := eq66280 X0
       grind)
    | exact resolve eq9 eq66280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66280
  have eq95362 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (k X0 (M.op X0 X0)) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq91203 X0
       grind)
    | exact superpose eq91203 eq9
    | (have j1 := eq91203 X0
       grind)
    | exact resolve eq9 eq91203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91203
  have eq95420 : ∀ X0 : G, (M.op (M.op (k X0 (M.op X0 X0)) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq95362 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95362
  have eq95475 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq95420 X0
       have i₂ := eq71259 X0 X1 X0
       grind)
    | exact superpose eq71259 eq95420
    | (have j0 := eq95420 X0
       have j1 := eq71259 X0 X1 x
       grind)
    | exact resolve eq95420 eq71259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71259 eq95420
  have eq95568 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X0) X1) X0)) = X0 := by
    intro X0 X1
    grind
  clear eq95475
  have eq106367 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq95568 X0 X1
       grind)
    | exact superpose eq95568 eq9
    | (have j1 := eq95568 X0 X1
       grind)
    | exact resolve eq9 eq95568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95568
  have eq106427 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq106367 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106367
  have eq106534 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (τ X0) = (k (τ X0) (M.op (M.op (M.op X1 (τ X0)) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq106427 (τ X0) X1
       grind)
    | exact superpose eq106427 eq30
    | (have j1 := eq106427 (τ X0) X1
       grind)
    | exact resolve eq30 eq106427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106427
  have eq106610 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (k (τ X0) (M.op (M.op (M.op X1 (τ X0)) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq106534 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq106534
    | (have j0 := eq106534 X0 X1
       grind)
    | exact resolve eq106534 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106534
  have eq107598 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (τ (τ X0)) = (k (τ (τ X0)) (M.op (M.op (M.op X1 (τ (τ X0))) X1) (τ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq106610 (τ X0) X1
       grind)
    | exact superpose eq106610 eq30
    | (have j1 := eq106610 (τ X0) X1
       grind)
    | exact resolve eq30 eq106610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106610
  have eq107678 : ∀ X0 X1 : G, (τ (τ X0)) = (k (τ (τ X0)) (M.op (M.op (M.op X1 (τ (τ X0))) X1) (τ (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq107598 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq107598
    | (have j0 := eq107598 X0 X1
       grind)
    | exact resolve eq107598 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107598
  have eq119469 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (M.op (M.op (M.op X1 (τ X0)) X1) (τ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq107678 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq107678
    | (have j0 := eq107678 (σ X0) X1
       grind)
    | exact resolve eq107678 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107678
  have eq119727 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (M.op (M.op (M.op X1 (τ X0)) X1) (τ X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq119469 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq119469
    | (have j0 := eq119469 X0 X1
       grind)
    | exact resolve eq119469 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119469
  have eq121026 : ∀ X0 : G, (τ X0) = (k (τ X0) (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq119727 X0 (τ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq119727
    | (have j0 := eq119727 X0 x
       grind)
    | exact resolve eq119727 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119727
  have eq122954 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ X0)))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ X0))
       have i₂ := eq121026 X0
       grind)
    | exact superpose eq121026 eq18
    | (have j1 := eq121026 X0
       grind)
    | exact resolve eq18 eq121026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq121026
  have eq123139 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (σ (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq122954 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq122954
    | (have j0 := eq122954 X0
       grind)
    | exact resolve eq122954 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122954
  have eq123331 : ∀ X0 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (τ X0) = (k (τ X0) (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) (τ (τ X0))) (τ (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq30 X0
       have i₂ := eq123139 (τ X0)
       grind)
    | exact superpose eq123139 eq30
    | (have j1 := eq123139 (τ X0)
       grind)
    | exact resolve eq30 eq123139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq123139
  have eq123613 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (k (τ X0) (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) (τ (τ X0))) (τ (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq123331 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq123331
    | (have j0 := eq123331 X0
       grind)
    | exact resolve eq123331 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123331
  have eq123636 : ∀ X0 : G, (τ X0) = (k (τ X0) (σ (M.op (M.op (τ (τ (M.op X0 X0))) (τ (τ X0))) (τ (τ X0))))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq123613 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq123613
    | (have j0 := eq123613 X0
       grind)
    | exact resolve eq123613 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq123613
  have eq189012 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4723 X2 X0 X1 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4723
  have eq189013 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq189012 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189012
  have eq189034 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189013 X0 X1 X2
       have i₂ := eq36 X0 X1 X2
       grind)
    | exact superpose eq36 eq189013
    | (have j0 := eq189013 X0 X1 X2
       grind)
    | exact resolve eq189013 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq189013
  have eq189035 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq189034 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189034
  have eq189546 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 (k X1 (τ X2))
       have i₂ := eq189035 X1 X2 (τ X0)
       grind)
    | exact superpose eq189035 eq19
    | (have j1 := eq189035 X1 X2 (τ X0)
       grind)
    | exact resolve eq19 eq189035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189035
  have eq189840 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189546 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq189546
    | (have j0 := eq189546 X0 X1 X2
       grind)
    | exact resolve eq189546 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189546
  have eq189978 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189840 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq189840
    | (have j0 := eq189840 X0 X1 X2
       grind)
    | exact resolve eq189840 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189840
  have eq190090 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189978 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq189978
    | (have j0 := eq189978 X0 X1 X2
       grind)
    | exact resolve eq189978 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189978
  have eq190307 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op X2 (k X0 X1)) ∨ (k X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq190090 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq190090
    | exact resolve eq190090 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190090
  have eq191519 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq191625 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq190307 (τ X0) (σ (M.op (M.op (τ (τ (M.op X0 X0))) (τ (τ X0))) (τ (τ X0)))) x
       have i₂ := eq123636 X0
       grind)
    | exact superpose eq123636 eq190307
    | (have j0 := eq190307 (τ X0) X1 (M.op X1 (τ X0))
       have j1 := eq123636 X0
       grind)
    | exact resolve eq190307 eq123636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123636 eq190307
  have eq193297 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (τ (σ X0)) = X1 ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0
       have i₂ := eq191625 (σ X0) X1
       grind)
    | exact superpose eq191625 eq22
    | (have j1 := eq191625 (σ X0) X1
       grind)
    | exact resolve eq22 eq191625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191625
  have eq193357 : ∀ X0 X1 : G, X0 = X1 ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq193297 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq193297
    | (have j0 := eq193297 X0 X1
       grind)
    | exact resolve eq193297 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193297
  have eq193383 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq193357 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq193357
    | (have j0 := eq193357 X0 X1
       grind)
    | exact resolve eq193357 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193357
  have eq193477 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq193383 X0 X1
       grind)
    | exact superpose eq193383 eq10
    | (have j1 := eq193383 X0 X1
       grind)
    | exact resolve eq10 eq193383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193383
  have eq193802 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq193477 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq193477
    | (have j0 := eq193477 X0 X1
       grind)
    | exact resolve eq193477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193477
  have eq194861 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ X0 = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq191519 X0 X1
       have i₂ := eq193802 X0 X1
       grind)
    | exact superpose eq193802 eq191519
    | (have j1 := eq193802 X0 X1
       grind)
    | exact resolve eq191519 eq193802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191519 eq193802
  have eq233375 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq194861 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194861
  have eq233376 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq233375 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233375
  have eq233377 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq233376 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233376
  have eq234830 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq233377 X1 (τ X0)
       grind)
    | exact superpose eq233377 eq19
    | (have j1 := eq233377 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq233377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq235073 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq233377 (σ X1) (σ X0)
       grind)
    | exact superpose eq233377 eq15
    | (have j1 := eq233377 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq233377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233377
  have eq237062 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq234830 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq234830
    | exact resolve eq234830 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234830
  have eq237471 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq237062 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq237062
    | (have j0 := eq237062 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq237062 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237062
  have eq241823 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq235073 x y
       grind)
    | exact superpose eq235073 eq16
    | (have j1 := eq235073 x y
       grind)
    | exact resolve eq16 eq235073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235073
  have eq242692 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq241823
       have i₂ := eq237471 x y
       grind)
    | exact superpose eq237471 eq241823
    | (have j1 := eq237471 (σ x) (σ y)
       grind)
    | (have r₁ := eq241823
       have r₂ := eq237471 x y
       grind)
    | (have r₁ := eq241823
       have r₂ := eq237471 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq241823
       have r₂ := eq237471 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq241823 eq237471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237471 eq241823
  have eq242695 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq242692
  have eq242699 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq242695
       grind)
    | exact superpose eq242695 eq16
    | exact resolve eq16 eq242695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242695
  have eq242700 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq242699
       have r₂ := eq22 x
       grind)
    | exact resolve eq242699 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242699
  have eq243598 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq242700
       grind)
    | exact superpose eq242700 eq16
    | exact resolve eq16 eq242700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243599 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq242700
       grind)
    | exact superpose eq242700 eq10
    | exact resolve eq10 eq242700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242700
  have eq243969 : x = y := by
    first
    | (have i₁ := eq243599
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq243599
    | exact resolve eq243599 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243599
  have eq243970 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq243598
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq243598
    | exact resolve eq243598 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq243598
  have eq243973 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq243970
       have i₂ := eq243969
       grind)
    | exact superpose eq243969 eq243970
    | exact resolve eq243970 eq243969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243969 eq243970
  have eq243974 : False := by grind
  exact eq243974

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pyy_x_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq54
    | (have j0 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 ∨ (M.op (M.op (M.op X1 X2) X0) X1) = (k (M.op (M.op (M.op X1 X2) X0) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (k (M.op (M.op (M.op X1 X2) X0) X1) X0) ∨ (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq81 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq132 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq148 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq132
       grind)
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq190 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq165 eq16
    | exact resolve eq16 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
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
  have eq250 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
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
  have eq852 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq60 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60
    | (have j0 := eq60 x X0 y
       grind)
    | exact resolve eq60 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq60
    | (have j0 := eq60 (σ x) X0 (σ y)
       grind)
    | exact resolve eq60 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq60 X1 X2 X0
       grind)
    | exact superpose eq60 eq54
    | exact resolve eq54 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq928 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq94 X0 X0 x
       have i₂ := eq54 X0 x
       grind)
    | exact superpose eq54 eq94
    | exact resolve eq94 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq946 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X1 (M.op X1 x) (M.op X1 x)
       have i₂ := eq14 (M.op X1 x) X1 x
       grind)
    | exact superpose eq14 eq94
    | exact resolve eq94 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq953 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq946 X0 X1
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq946
    | (have j0 := eq946 X0 X1
       grind)
    | exact resolve eq946 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq946
  have eq971 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq928 X0
       have j1 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq928 x
       have r₂ := eq13 (M.op x x) x
       grind)
    | exact resolve eq928 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq6344 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq228 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq228
    | (have j0 := eq228 y
       grind)
    | exact resolve eq228 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq6379 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6344
  have eq6386 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6379
       have i₂ := eq132
       grind)
    | exact superpose eq132 eq6379
    | exact resolve eq6379 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq6379
  have eq6410 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6386
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6386 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6386
  have eq6441 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6410 eq148
    | exact resolve eq148 eq6410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq6410
  have eq6626 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq250
    | (have j0 := eq250 (M.op x y)
       grind)
    | exact resolve eq250 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq6660 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6626
  have eq6666 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq165 eq6660
    | exact resolve eq6660 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq6660
  have eq6697 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6666
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6666 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6666
  have eq6746 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq6697 eq190
    | exact resolve eq190 eq6697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq6697
  have eq19823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq120 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq19831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq19823
    | exact resolve eq19823 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19823
  have eq19842 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq19831
       have r₂ := eq27
       grind)
    | exact resolve eq19831 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19831
  have eq19844 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq19842
    | exact resolve eq19842 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19842
  have eq19853 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq19844 eq57
    | exact resolve eq57 eq19844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19844
  have eq19937 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq19853 x
       have i₂ := eq54 sF3 x
       grind)
    | exact superpose eq54 eq19853
    | exact resolve eq19853 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19853
  have eq21499 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq19937 eq26
    | (have j1 := eq19937 (σ x)
       grind)
    | exact resolve eq26 eq19937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19937
  have eq21517 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21499
  have eq21539 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq57 X0 y x
       have i₂ := eq21517
       grind)
    | exact superpose eq21517 eq57
    | exact resolve eq57 eq21517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21517
  have eq21623 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq21539 x
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq21539
    | exact resolve eq21539 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21539
  have eq23771 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21623 x
       grind)
    | exact superpose eq21623 eq18
    | (have j1 := eq21623 x
       grind)
    | exact resolve eq18 eq21623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21623
  have eq23794 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq23771
  have eq23812 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23794 eq86
    | (have r₁ := eq86
       have r₂ := eq23794
       grind)
    | exact resolve eq86 eq23794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq23794
  have eq23834 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq23812
  have eq25810 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23834 eq54
    | exact resolve eq54 eq23834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23834
  have eq25945 : (τ (σ y)) = (k y y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25810 eq6441
    | exact resolve eq6441 eq25810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6441 eq25810
  have eq26041 : (σ x) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq25945
    | exact resolve eq25945 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25945
  have eq26273 : (τ (σ x)) = (k x y) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26041 eq80
    | exact resolve eq80 eq26041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq26041
  have eq26305 : y = (k y y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq26273
    | exact resolve eq26273 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq26273
  have eq26403 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq26305
       grind)
    | exact superpose eq26305 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq26305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26305
  have eq26422 : y = (M.op y y) ∨ x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq26403
  have eq26468 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq57 X0 y y
       have i₂ := eq26422
       grind)
    | exact superpose eq26422 eq57
    | exact resolve eq57 eq26422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26422
  have eq26545 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26468 x
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq26468
    | exact resolve eq26468 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26468
  have eq26751 : y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq26545 x
       grind)
    | exact superpose eq26545 eq18
    | (have j1 := eq26545 x
       grind)
    | exact resolve eq18 eq26545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26545
  have eq26778 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq26751
  have eq26796 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq26778
       grind)
    | exact superpose eq26778 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq26778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26778
  have eq26814 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26796
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26796
    | exact resolve eq26796 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26796
  have eq26831 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26814
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26814
    | exact resolve eq26814 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26814
  have eq26832 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq26831
  have eq26919 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq57 X0 y x
       have i₂ := eq26832
       grind)
    | exact superpose eq26832 eq57
    | exact resolve eq57 eq26832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq26832
  have eq27017 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26919 x
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq26919
    | exact resolve eq26919 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26919
  have eq27865 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq27017 x
       grind)
    | exact superpose eq27017 eq18
    | (have j1 := eq27017 x
       grind)
    | exact resolve eq18 eq27017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27017
  have eq27892 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq27865
  have eq27903 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27892 eq20
    | exact resolve eq20 eq27892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27906 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27892 eq55
    | exact resolve eq55 eq27892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27997 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq27892
  have eq28052 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27903
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27903
    | exact resolve eq27903 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27903
  have eq28098 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28052 eq26
    | exact resolve eq26 eq28052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28330 : x = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq953 y x
       have i₂ := eq27906
       grind)
    | exact superpose eq27906 eq953
    | (have j0 := eq953 x y
       grind)
    | exact resolve eq953 eq27906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq27906
  have eq28346 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq28330
       have r₂ := eq27997
       grind)
    | exact resolve eq28330 eq27997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27997 eq28330
  have eq28428 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq28346
       grind)
    | exact superpose eq28346 eq44
    | exact resolve eq44 eq28346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq28346
  have eq28461 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28428
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28428
    | exact resolve eq28428 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28428
  have eq28622 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28461 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq28461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28461
  have eq28639 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq28622
    | exact resolve eq28622 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28622
  have eq28652 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq28639
    | exact resolve eq28639 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28639
  have eq521376 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28052 eq28652
    | exact resolve eq28652 eq28052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28652
  have eq521708 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq521376
  have eq521933 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq521708
       have r₂ := eq27
       grind)
    | exact resolve eq521708 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521708
  have eq522047 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) = (M.op X0 (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq521933 eq889
    | exact resolve eq889 eq521933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq521933
  have eq522455 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq522047 x
       have i₂ := eq54 sF1 x
       grind)
    | exact superpose eq54 eq522047
    | exact resolve eq522047 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq522047
  have eq523724 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq522455 eq28098
    | exact resolve eq28098 eq522455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28098 eq522455
  have eq523801 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq523724
  have eq523834 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq523801
       have r₂ := eq27
       grind)
    | exact resolve eq523801 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523801
  have eq523864 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq523834 eq56
    | exact resolve eq56 eq523834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523834
  have eq524151 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq523864 eq856
    | exact resolve eq856 eq523864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856 eq523864
  have eq524571 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56 eq524151
    | exact resolve eq524151 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq524151
  have eq524616 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq524571
    | exact resolve eq524571 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524571
  have eq525170 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq524616 eq27
    | exact resolve eq27 eq524616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524616
  have eq525346 : x = (M.op x y) := by
    first
    | (have r₁ := eq525170
       have r₂ := eq28052
       grind)
    | exact resolve eq525170 eq28052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28052 eq525170
  have eq525349 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq525346 eq20
    | exact resolve eq20 eq525346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq525352 : x = (M.op x x) := by
    first
    | exact superpose eq525346 eq55
    | exact resolve eq55 eq525346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525968 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq525349
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq525349
    | exact resolve eq525349 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525349
  have eq526031 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq525968 eq26
    | exact resolve eq26 eq525968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq526759 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq852 x
       have i₂ := eq525352
       grind)
    | exact superpose eq525352 eq852
    | exact resolve eq852 eq525352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq526786 : x = (k x x) := by
    first
    | (have i₁ := eq971 x
       have i₂ := eq525352
       grind)
    | exact superpose eq525352 eq971
    | exact resolve eq971 eq525352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971 eq525352
  have eq527191 : y = (M.op x y) := by
    first
    | exact superpose eq55 eq526759
    | exact resolve eq526759 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq526759
  have eq527258 : y = (M.op x y) := by
    first
    | (have i₁ := eq527191
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq527191
    | exact resolve eq527191 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq527191
  have eq527280 : x = y := by
    first
    | exact superpose eq525346 eq527258
    | exact resolve eq527258 eq525346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527258
  have eq527303 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq527280
       grind)
    | exact superpose eq527280 eq24
    | exact resolve eq24 eq527280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq527280
  have eq528092 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq527303
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq527303
    | exact resolve eq527303 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527303
  have eq528249 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq525968 eq528092
    | exact resolve eq528092 eq525968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528092
  have eq536288 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq528249 eq526031
    | exact resolve eq526031 eq528249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526031 eq528249
  have eq553430 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq536288 eq6746
    | exact resolve eq6746 eq536288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6746 eq536288
  have eq553969 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq525346 eq553430
    | exact resolve eq553430 eq525346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525346 eq553430
  have eq554113 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq553969
       have i₂ := eq526786
       grind)
    | exact superpose eq526786 eq553969
    | exact resolve eq553969 eq526786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526786 eq553969
  have eq554485 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq554113 eq15
    | exact resolve eq15 eq554113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554113
  have eq555124 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq554485
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq554485
    | exact resolve eq554485 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq554485
  have eq555310 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq525968 eq555124
    | exact resolve eq555124 eq525968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525968 eq555124
  have eq555416 : False := by grind
  exact eq555416

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pxx_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq54
    | (have j0 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq98 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq100 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq102 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq102 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq102 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq106 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq103 x
       grind)
    | exact superpose eq103 eq43
    | exact resolve eq43 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq107 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq103 sF2
       grind)
    | exact superpose eq103 eq49
    | exact resolve eq49 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq108 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq107
       have i₂ := eq103 x
       grind)
    | exact superpose eq103 eq107
    | exact resolve eq107 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq109 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq103 sF2
       grind)
    | exact superpose eq103 eq106
    | exact resolve eq106 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq106
  have eq123 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq132 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq123
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq123
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq123 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq132
    | exact resolve eq132 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq139 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq138
    | exact resolve eq138 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq140 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq139
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq139
    | exact resolve eq139 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq141 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq140
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq140
    | exact resolve eq140 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq1130 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq60 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60
    | (have j0 := eq60 x X0 y
       grind)
    | exact resolve eq60 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1134 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq60
    | (have j0 := eq60 (σ x) X0 (σ y)
       grind)
    | exact resolve eq60 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq12225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq141 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12225
    | exact resolve eq12225 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12225
  have eq12237 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12226
       have r₂ := eq27
       grind)
    | exact resolve eq12226 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12226
  have eq12241 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12237
    | exact resolve eq12237 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12237
  have eq12243 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12241
    | exact resolve eq12241 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12241
  have eq12424 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12243 eq100
    | (have r₁ := eq100
       have r₂ := eq12243
       grind)
    | exact resolve eq100 eq12243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq12243
  have eq12481 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq12424
  have eq12482 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq12481
  have eq12497 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12482 eq141
    | exact resolve eq141 eq12482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq12482
  have eq12509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12497
  have eq12511 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12509
       have r₂ := eq27
       grind)
    | exact resolve eq12509 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12509
  have eq12513 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq12511
       grind)
    | exact superpose eq12511 eq98
    | (have r₁ := eq98
       have r₂ := eq12511
       grind)
    | exact resolve eq98 eq12511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq12514 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq12511
       grind)
    | exact superpose eq12511 eq109
    | exact resolve eq109 eq12511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12511
  have eq12570 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12513
  have eq12571 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12570
  have eq12586 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq12514
    | exact resolve eq12514 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12514
  have eq12593 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq12571
       grind)
    | exact superpose eq12571 eq123
    | exact resolve eq123 eq12571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq12571
  have eq12615 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq12593
    | exact resolve eq12593 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12593
  have eq13726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12615 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq12615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12615
  have eq13729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13726
    | exact resolve eq13726 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13726
  have eq13740 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13729
       have r₂ := eq27
       grind)
    | exact resolve eq13729 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13729
  have eq13744 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13740
    | exact resolve eq13740 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13740
  have eq13746 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13744
    | exact resolve eq13744 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13744
  have eq13747 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13746
  have eq14608 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13747 eq12586
    | exact resolve eq12586 eq13747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12586 eq13747
  have eq14659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14608
  have eq14670 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14659
       have r₂ := eq27
       grind)
    | exact resolve eq14659 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14659
  have eq14676 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14670 eq56
    | exact resolve eq56 eq14670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15033 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14676 eq108
    | exact resolve eq108 eq14676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq15044 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14676 eq1134
    | exact resolve eq1134 eq14676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134 eq14676
  have eq15124 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56 eq15044
    | exact resolve eq15044 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq15044
  have eq15132 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq15033
    | exact resolve eq15033 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15033
  have eq15145 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15124
    | exact resolve eq15124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15124
  have eq15496 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15145 eq14670
    | exact resolve eq14670 eq15145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14670 eq15145
  have eq15497 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq15496
  have eq16529 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15497 eq29
    | exact resolve eq29 eq15497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15497
  have eq16648 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq16529
    | exact resolve eq16529 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16529
  have eq18847 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1130 x
       have i₂ := eq15132
       grind)
    | exact superpose eq15132 eq1130
    | exact resolve eq1130 eq15132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15132
  have eq18931 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55 eq18847
    | exact resolve eq18847 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18847
  have eq18952 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18931
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18931
    | exact resolve eq18931 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18931
  have eq19579 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq18952
  have eq19581 : x = (M.op x y) := by
    first
    | (have r₁ := eq19579
       have r₂ := eq16648
       grind)
    | exact resolve eq19579 eq16648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16648 eq19579
  have eq19653 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq19581 eq20
    | exact resolve eq20 eq19581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq19656 : x = (M.op x x) := by
    first
    | exact superpose eq19581 eq55
    | exact resolve eq55 eq19581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19793 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19653
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19653
    | exact resolve eq19653 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19653
  have eq19811 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq19793 eq26
    | exact resolve eq26 eq19793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq19990 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq19656
       grind)
    | exact superpose eq19656 eq109
    | exact resolve eq109 eq19656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq19999 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq1130 x
       have i₂ := eq19656
       grind)
    | exact superpose eq19656 eq1130
    | exact resolve eq1130 eq19656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq19656
  have eq20082 : y = (M.op x y) := by
    first
    | exact superpose eq55 eq19999
    | exact resolve eq19999 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq19999
  have eq20089 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq19793 eq19990
    | exact resolve eq19990 eq19793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19990
  have eq20103 : y = (M.op x y) := by
    first
    | (have i₁ := eq20082
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20082
    | exact resolve eq20082 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq20082
  have eq20110 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq20089
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20089
    | exact resolve eq20089 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20089
  have eq20117 : x = y := by
    first
    | exact superpose eq19581 eq20103
    | exact resolve eq20103 eq19581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19581 eq20103
  have eq20123 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq19793 eq20110
    | exact resolve eq20110 eq19793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20110
  have eq20138 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq20117
       grind)
    | exact superpose eq20117 eq24
    | exact resolve eq24 eq20117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq20117
  have eq20258 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20138
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20138
    | exact resolve eq20138 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20138
  have eq20312 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19793 eq20258
    | exact resolve eq20258 eq19793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19793 eq20258
  have eq21664 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20312 eq19811
    | exact resolve eq19811 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19811 eq20312
  have eq22634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20123 eq21664
    | exact resolve eq21664 eq20123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20123 eq21664
  have eq22635 : False := by grind
  exact eq22635
