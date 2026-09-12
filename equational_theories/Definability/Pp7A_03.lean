import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1242`: `x = x ◇ (((y ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation1242 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1242 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1242.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq263 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) ≠ (M.op X2 X0) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq13 X2 X0
       grind)
    | exact superpose eq13 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq13 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X2 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq263 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq1877 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq264 X1 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1938 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1877 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq1939 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1938 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938
  have eq2092 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq1939 (τ X0)
       grind)
    | exact superpose eq1939 eq31
    | exact resolve eq31 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2139 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2092 X0
       have i₂ := eq1939 X0
       grind)
    | exact superpose eq1939 eq2092
    | exact resolve eq2092 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939 eq2092
  have eq2317 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq2139 X0
       grind)
    | exact superpose eq2139 eq14
    | (have j0 := eq14 (τ X0) X1
       grind)
    | exact resolve eq14 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2319 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq2139 X0
       grind)
    | exact superpose eq2139 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139
  have eq2322 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2317 X0 X1
       have j1 := eq2319 X0 X1
       grind)
    | (have r₁ := eq2317 X0 X1
       have r₂ := eq2319 X0 X1
       grind)
    | exact resolve eq2317 eq2319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2317 eq2319
  have eq2443 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2322 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2322
    | exact resolve eq2322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2322
  have eq2494 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq264 X1 X1 X0
       have i₂ := eq2443 X0 X1
       grind)
    | (have i₁ := eq264 X0 X1 X1
       have i₂ := eq2443 X0 X1
       grind)
    | exact superpose eq2443 eq264
    | (have j0 := eq264 X1 X2 X2
       have j1 := eq2443 X1 X2
       grind)
    | (have r₁ := eq264 X1 X1 X0
       have r₂ := eq2443 X0 X1
       grind)
    | (have r₁ := eq264 X0 X1 X1
       have r₂ := eq2443 X0 X1
       grind)
    | exact resolve eq264 eq2443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq2443
  have eq2507 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2494 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2494
  have eq2508 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2507 X2 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2507
  have eq2613 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2508 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2508
  have eq2614 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2613 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2613
  have eq2653 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2614 (σ X0) (σ X1)
       grind)
    | exact superpose eq2614 eq15
    | exact resolve eq15 eq2614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2768 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2653 X0 X1
       have i₂ := eq2614 X0 X1
       grind)
    | exact superpose eq2614 eq2653
    | exact resolve eq2653 eq2614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2614 eq2653
  have eq3910 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2768 x y
       grind)
    | exact superpose eq2768 eq16
    | (have r₁ := eq16
       have r₂ := eq2768 x y
       grind)
    | exact resolve eq16 eq2768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768
  have eq3927 : False := by grind
  exact eq3927

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation1434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq76 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq79 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq44
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq82 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq76 sF2
       grind)
    | exact superpose eq76 eq79
    | exact resolve eq79 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq79
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X0) X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X0)
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq45
    | (have j1 := eq92 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq45 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq115
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq115
    | exact resolve eq115 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq121
    | exact resolve eq121 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq185 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq122 eq92
    | (have j0 := eq92 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq92 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq122
  have eq186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq185
    | exact resolve eq185 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq189 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq186
       have r₂ := eq28
       grind)
    | exact resolve eq186 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq192 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq189 eq30
    | exact resolve eq30 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq189
  have eq205 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq192
    | exact resolve eq192 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq192
  have eq206 : x = y := by grind
  clear eq205
  have eq209 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq206
       grind)
    | exact superpose eq206 eq19
    | exact resolve eq19 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq210 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq206
       grind)
    | exact superpose eq206 eq25
    | exact resolve eq25 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq206
  have eq221 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq210
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq210
    | exact resolve eq210 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq210
  have eq225 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq221 eq27
    | exact resolve eq27 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq221
  have eq239 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq209
       grind)
    | exact superpose eq209 eq82
    | exact resolve eq82 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq209
  have eq244 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq239
    | exact resolve eq239 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq239
  have eq250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq225 eq244
    | exact resolve eq244 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq244
  have eq251 : False := by grind
  exact eq251

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation1434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq85 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq85 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq13 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq279 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq280 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq279 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq285 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq280
    | (have j0 := eq280 X0 X1
       grind)
    | exact resolve eq280 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq286 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq285 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq570 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq286
    | exact resolve eq286 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq598 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq570 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq570
    | (have j0 := eq570 X0 X1
       grind)
    | exact resolve eq570 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq570
  have eq600 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq598 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq598
    | exact resolve eq598 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq661 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq600 (τ X0) X1
       grind)
    | exact superpose eq600 eq18
    | (have j1 := eq600 (τ X0) X1
       grind)
    | exact resolve eq18 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq600
  have eq806 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq661 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq661
    | exact resolve eq661 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq851 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq806 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq806
    | (have j0 := eq806 X0 X1
       grind)
    | exact resolve eq806 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq964 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq578
       have i₂ := eq851 x y
       grind)
    | exact superpose eq851 eq578
    | (have j1 := eq851 (σ x) (σ y)
       grind)
    | (have r₁ := eq578
       have r₂ := eq851 x y
       grind)
    | exact resolve eq578 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq965 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq964
  have eq997 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq965
  have eq1011 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq578
       have i₂ := eq997
       grind)
    | exact superpose eq997 eq578
    | exact resolve eq578 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq997
  have eq1012 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1011
  have eq1013 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1012
  have eq1041 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1013
  have eq1059 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1041
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1041
    | exact resolve eq1041 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1064 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1059
       grind)
    | exact superpose eq1059 eq16
    | exact resolve eq16 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1124 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1064
       have i₂ := eq851 x y
       grind)
    | exact superpose eq851 eq1064
    | (have j1 := eq851 x y
       grind)
    | (have r₁ := eq1064
       have r₂ := eq851 x y
       grind)
    | exact resolve eq1064 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq1125 : x = (M.op y y) := by grind
  clear eq1124
  have eq1130 : (M.op x y) = (k x y) := by grind
  clear eq1125
  have eq1182 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1064
       have i₂ := eq1130
       grind)
    | exact superpose eq1130 eq1064
    | exact resolve eq1064 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064 eq1130
  have eq1185 : False := by grind
  exact eq1185

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation1434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq85 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq271 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq85 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq13 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq283 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq284 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq283 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq288 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq284
    | (have j0 := eq284 X0 X1
       grind)
    | exact resolve eq284 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq289 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq288 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq565 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq289 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq289
    | exact resolve eq289 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  clear eq289
  have eq600 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq565
    | (have j0 := eq565 X0 X1
       grind)
    | exact resolve eq565 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq565
  have eq601 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq600 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq600
    | exact resolve eq600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq662 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq601 (τ X1) X0
       grind)
    | exact superpose eq601 eq18
    | (have j1 := eq601 (τ X1) X0
       grind)
    | exact resolve eq18 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq601
  have eq809 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq662 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq662
    | exact resolve eq662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq855 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq809 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq809
    | (have j0 := eq809 X0 X1
       grind)
    | exact resolve eq809 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq966 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq579
       have i₂ := eq855 y x
       grind)
    | exact superpose eq855 eq579
    | (have j1 := eq855 (σ y) (σ x)
       grind)
    | (have r₁ := eq579
       have r₂ := eq855 y x
       grind)
    | exact resolve eq579 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq966
  have eq999 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq967
  have eq1013 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq579
       have i₂ := eq999
       grind)
    | exact superpose eq999 eq579
    | exact resolve eq579 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq999
  have eq1014 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1013
  have eq1015 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1014
  have eq1043 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1015
  have eq1061 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1043
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1043
    | exact resolve eq1043 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1066 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1061
       grind)
    | exact superpose eq1061 eq16
    | exact resolve eq16 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq1113 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1066
       have i₂ := eq855 y x
       grind)
    | exact superpose eq855 eq1066
    | (have j1 := eq855 y x
       grind)
    | (have r₁ := eq1066
       have r₂ := eq855 y x
       grind)
    | exact resolve eq1066 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq1114 : y = (M.op x x) := by grind
  clear eq1113
  have eq1119 : (M.op x y) = (k y x) := by grind
  clear eq1114
  have eq1173 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1066
       have i₂ := eq1119
       grind)
    | exact superpose eq1119 eq1066
    | exact resolve eq1066 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066 eq1119
  have eq1176 : False := by grind
  exact eq1176

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation1434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
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
  have eq36 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq40 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq40 X1 X0
       grind)
    | (have r₁ := eq45 X1 X0
       have r₂ := eq40 X0 X1
       grind)
    | exact resolve eq45 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq45
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq51
  have eq101 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq105 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq101 X0 X1
       have j1 := eq54 X0 X1
       grind)
    | (have r₁ := eq101 X0 X1
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq101 X1 X1
       have r₂ := eq54 X1 X1
       grind)
    | exact resolve eq101 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq101
  have eq385 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq105 (σ X0) (σ X1)
       grind)
    | exact superpose eq105 eq15
    | exact resolve eq15 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq385 X0 X1
       have i₂ := eq105 X0 X1
       grind)
    | exact superpose eq105 eq385
    | exact resolve eq385 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq385
  have eq392 : False := by grind
  exact eq392

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation1434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq84 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq84
    | (have j0 := eq84 X0
       grind)
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq84
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
    | (have r₁ := eq93 x
       have r₂ := eq12 X0 x
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
  clear eq97
  have eq124 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78 x y
       grind)
    | exact superpose eq78 eq16
    | (have j1 := eq78 x y
       grind)
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq237 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq229
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq229
    | exact resolve eq229 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq728 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq80
    | (have j0 := eq80 X1 X1
       grind)
    | exact resolve eq80 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq769 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq728 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq728
    | (have j0 := eq728 X0 X1
       grind)
    | exact resolve eq728 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq804 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq237
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq237
    | (have j1 := eq14 (σ x) (σ (M.op x x))
       grind)
    | (have r₁ := eq237
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq237
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq237 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq805 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq804
  have eq4526 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq805
       grind)
    | exact superpose eq805 eq16
    | exact resolve eq16 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq4527 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4526
       have r₂ := eq108 x
       grind)
    | exact resolve eq4526 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4526
  have eq4532 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq124 x X0
       have i₂ := eq4527
       grind)
    | exact superpose eq4527 eq124
    | (have j0 := eq124 x X0
       grind)
    | (have r₁ := eq124 x x
       have r₂ := eq4527
       grind)
    | exact resolve eq124 eq4527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4527
  have eq4555 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq4532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4532
  have eq4561 : ∀ X0 : G, (σ x) = (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq4555 X0
       have j1 := eq124 x X0
       grind)
    | (have r₁ := eq4555 X0
       have r₂ := eq124 x x
       grind)
    | exact resolve eq4555 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq4555
  have eq4673 : ∀ X0 : G, y = (τ (σ x)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq4561 X0
       grind)
    | exact superpose eq4561 eq10
    | (have j1 := eq4561 X0
       grind)
    | exact resolve eq10 eq4561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4561
  have eq4733 : ∀ X0 : G, x = y ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq4673 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4673
    | (have j0 := eq4673 X0
       grind)
    | exact resolve eq4673 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4673
  have eq4744 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq4733 X0
       grind)
    | exact superpose eq4733 eq16
    | (have j1 := eq4733 X0
       grind)
    | exact resolve eq16 eq4733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4733
  have eq4745 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq4744 X0
       grind)
    | (have r₁ := eq4744 X0
       have r₂ := eq108 x
       grind)
    | exact resolve eq4744 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq4744
  have eq4832 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq4745 (σ X0)
       grind)
    | exact superpose eq4745 eq15
    | exact resolve eq15 eq4745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4745
  have eq5140 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4832 y
       grind)
    | exact superpose eq4832 eq16
    | exact resolve eq16 eq4832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4832
  have eq5249 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5140
       have i₂ := eq769 y x
       grind)
    | exact superpose eq769 eq5140
    | (have j1 := eq769 x y
       grind)
    | (have r₁ := eq5140
       have r₂ := eq769 y x
       grind)
    | (have r₁ := eq5140
       have r₂ := eq769 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5140
       have r₂ := eq769 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5140 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq5250 : x = y ∨ x = (M.op x x) := by grind
  clear eq5249
  have eq5331 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5140
       have i₂ := eq5250
       grind)
    | exact superpose eq5250 eq5140
    | exact resolve eq5140 eq5250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5250
  have eq5332 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5331
       have i₂ := eq94 x
       grind)
    | exact superpose eq94 eq5331
    | exact resolve eq5331 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq5331
  have eq5333 : x = (M.op x x) := by grind
  clear eq5332
  have eq5336 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq5333
       grind)
    | exact superpose eq5333 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq5333
       grind)
    | exact resolve eq12 eq5333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5333
  have eq5363 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq5336 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5336
  have eq5512 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq5140
       have i₂ := eq5363 y
       grind)
    | exact superpose eq5363 eq5140
    | exact resolve eq5140 eq5363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5140 eq5363
  have eq5515 : False := by grind
  exact eq5515

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation1434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq97 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq241 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq95 x y
       grind)
    | exact superpose eq95 eq16
    | (have j1 := eq95 x y
       grind)
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq647 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq685 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq647 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq647
    | (have j0 := eq647 X0 X1
       grind)
    | exact resolve eq647 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq781 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq246 (τ X1) (τ X0)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq246
    | (have j0 := eq246 (τ X1) (τ X0)
       grind)
    | exact resolve eq246 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq789 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq781 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq781
    | (have j0 := eq781 X0 X1
       grind)
    | exact resolve eq781 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq792 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq789 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq789
    | (have j0 := eq789 X0 X1
       grind)
    | exact resolve eq789 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq794 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq792 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq792
    | (have j0 := eq792 X0 X1
       grind)
    | exact resolve eq792 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq795 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq794 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq794
    | (have j0 := eq794 X0 X1
       grind)
    | exact resolve eq794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq796 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq795
    | (have j0 := eq795 X0 X1
       grind)
    | exact resolve eq795 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq797 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq796 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq796
    | (have j0 := eq796 X0 X1
       grind)
    | exact resolve eq796 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq912 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq241
       have i₂ := eq685 y x
       grind)
    | exact superpose eq685 eq241
    | (have j1 := eq685 (σ y) (σ x)
       grind)
    | (have r₁ := eq241
       have r₂ := eq685 y x
       grind)
    | (have r₁ := eq241
       have r₂ := eq685 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq241
       have r₂ := eq685 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq241 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq685
  have eq913 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq912
  have eq6760 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq913
       grind)
    | exact superpose eq913 eq16
    | exact resolve eq16 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq6761 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq6760
       have r₂ := eq22 x
       grind)
    | exact resolve eq6760 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6760
  have eq6924 : x ≠ x ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq6761
       grind)
    | exact superpose eq6761 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6761
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq6761
       grind)
    | exact resolve eq13 eq6761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6761
  have eq6926 : x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6924
  have eq9055 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6926
       grind)
    | exact superpose eq6926 eq16
    | exact resolve eq16 eq6926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6926
  have eq9056 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq9055
       have r₂ := eq22 x
       grind)
    | exact resolve eq9055 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9055
  have eq9158 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq9056
       grind)
    | exact superpose eq9056 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq9056
       grind)
    | exact resolve eq13 eq9056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9056
  have eq9163 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq9158
  have eq9164 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq9163
  have eq9170 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9164
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9164
    | exact resolve eq9164 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9164
  have eq9293 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq246 x y
       have i₂ := eq9170
       grind)
    | exact superpose eq9170 eq246
    | (have j0 := eq246 x y
       grind)
    | (have r₁ := eq246 x y
       have r₂ := eq9170
       grind)
    | exact resolve eq246 eq9170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9170
  have eq9315 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq9293
  have eq9316 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq9315
  have eq9321 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq246 x y
       grind)
    | (have r₁ := eq9316
       have r₂ := eq246 x y
       grind)
    | exact resolve eq9316 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq9316
  have eq9325 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9321
       grind)
    | exact superpose eq9321 eq16
    | exact resolve eq16 eq9321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9328 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq9321
       grind)
    | exact superpose eq9321 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq9321
       grind)
    | exact resolve eq13 eq9321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9321
  have eq9333 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq9328
  have eq9334 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq9333
  have eq9340 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9334
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9334
    | exact resolve eq9334 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9334
  have eq9461 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9340
       grind)
    | exact superpose eq9340 eq10
    | exact resolve eq10 eq9340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9340
  have eq9545 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9461
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9461
    | exact resolve eq9461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9461
  have eq9718 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9545
       grind)
    | exact superpose eq9545 eq16
    | exact resolve eq16 eq9545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9545
  have eq9719 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq9718
       have r₂ := eq22 x
       grind)
    | exact resolve eq9718 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9718
  have eq9731 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq9719
       grind)
    | exact superpose eq9719 eq10
    | exact resolve eq10 eq9719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9719
  have eq9818 : x = (k y x) := by
    first
    | (have i₁ := eq9731
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9731
    | exact resolve eq9731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9731
  have eq10007 : x ≠ x ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq797 y x
       have i₂ := eq9818
       grind)
    | exact superpose eq9818 eq797
    | (have j0 := eq797 y x
       grind)
    | (have r₁ := eq797 y x
       have r₂ := eq9818
       grind)
    | exact resolve eq797 eq9818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797 eq9818
  have eq10020 : x = (M.op x y) ∨ x = y := by grind
  clear eq10007
  have eq10024 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9325
       have i₂ := eq10020
       grind)
    | exact superpose eq10020 eq9325
    | exact resolve eq9325 eq10020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9325 eq10020
  have eq10035 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq10024
  have eq10240 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10035
       grind)
    | exact superpose eq10035 eq16
    | exact resolve eq16 eq10035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10035
  have eq10245 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq10240
       have r₂ := eq22 x
       grind)
    | exact resolve eq10240 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10240
  have eq10246 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10245
       grind)
    | exact superpose eq10245 eq16
    | exact resolve eq16 eq10245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10247 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10245
       grind)
    | exact superpose eq10245 eq10
    | exact resolve eq10 eq10245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10245
  have eq10335 : x = y := by
    first
    | (have i₁ := eq10247
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10247
    | exact resolve eq10247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10247
  have eq10336 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10246
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq10246
    | exact resolve eq10246 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10246
  have eq10337 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10336
       have i₂ := eq10335
       grind)
    | exact superpose eq10335 eq10336
    | exact resolve eq10336 eq10335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10335 eq10336
  have eq10338 : False := by grind
  exact eq10338

/-- `Equation1437`: `x = (x ◇ x) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation1437 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1437 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1437.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq61 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (k (σ X0) X1)
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq97 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq102 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq246 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq102 x y
       grind)
    | exact superpose eq102 eq16
    | (have j1 := eq102 x y
       grind)
    | exact resolve eq16 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq1107 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq96 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1152 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1107 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1107
    | (have j0 := eq1107 X0 X1
       grind)
    | exact resolve eq1107 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1577 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq246
       have i₂ := eq1152 x y
       grind)
    | exact superpose eq1152 eq246
    | (have j1 := eq1152 x y
       grind)
    | (have r₁ := eq246
       have r₂ := eq1152 x y
       grind)
    | (have r₁ := eq246
       have r₂ := eq1152 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq246
       have r₂ := eq1152 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq246 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1578 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq1577
  have eq1699 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq254 (τ X1) (τ X0)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq254
    | (have j0 := eq254 (τ X1) (τ X0)
       grind)
    | exact resolve eq254 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq254
  have eq1718 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1699 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1699
    | (have j0 := eq1699 X0 X1
       grind)
    | exact resolve eq1699 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699
  have eq1730 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1718 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq1718
    | (have j0 := eq1718 X0 X1
       grind)
    | exact resolve eq1718 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq1739 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1730 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1730
    | (have j0 := eq1730 X0 X1
       grind)
    | exact resolve eq1730 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq1743 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1739 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1739
    | (have j0 := eq1739 X0 X1
       grind)
    | exact resolve eq1739 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739
  have eq1746 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1743 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq1743
    | (have j0 := eq1743 X0 X1
       grind)
    | exact resolve eq1743 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1743
  have eq1748 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1746 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1746
    | (have j0 := eq1746 X0 X1
       grind)
    | exact resolve eq1746 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746
  have eq1749 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1748 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1748
    | (have j0 := eq1748 X0 X1
       grind)
    | exact resolve eq1748 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748
  have eq21691 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1578
       grind)
    | exact superpose eq1578 eq16
    | exact resolve eq16 eq1578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq21692 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq21691
       have r₂ := eq22 x
       grind)
    | exact resolve eq21691 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21691
  have eq21699 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61 y (σ x)
       have i₂ := eq21692
       grind)
    | exact superpose eq21692 eq61
    | (have j0 := eq61 y (σ x)
       grind)
    | (have r₁ := eq61 y (σ x)
       have r₂ := eq21692
       grind)
    | exact resolve eq61 eq21692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq21692
  have eq21727 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq21699
  have eq21728 : (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq21727
  have eq21742 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq21728
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq21728
    | exact resolve eq21728 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21728
  have eq21987 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21742
       grind)
    | exact superpose eq21742 eq10
    | exact resolve eq10 eq21742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21742
  have eq22093 : x = y ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq21987
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21987
    | exact resolve eq21987 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21987
  have eq22299 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22093
       grind)
    | exact superpose eq22093 eq16
    | exact resolve eq16 eq22093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22093
  have eq22300 : (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq22299
       have r₂ := eq22 x
       grind)
    | exact resolve eq22299 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22299
  have eq22311 : (k y x) = (τ (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq22300
       grind)
    | exact superpose eq22300 eq10
    | exact resolve eq10 eq22300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22300
  have eq22423 : (k y x) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq22311
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq22311
    | exact resolve eq22311 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22311
  have eq22677 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1749 y x
       have i₂ := eq22423
       grind)
    | exact superpose eq22423 eq1749
    | (have j0 := eq1749 y x
       grind)
    | (have r₁ := eq1749 y x
       have r₂ := eq22423
       grind)
    | exact resolve eq1749 eq22423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749 eq22423
  have eq22706 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq22677
  have eq22707 : x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq22706
  have eq22716 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22707
       grind)
    | exact superpose eq22707 eq16
    | exact resolve eq16 eq22707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22707
  have eq22717 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq22716
       have r₂ := eq22 x
       grind)
    | exact resolve eq22716 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22716
  have eq22974 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq22717
       grind)
    | exact superpose eq22717 eq13
    | (have j0 := eq13 (M.op x y) (k y X0)
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22717
       grind)
    | exact resolve eq13 eq22717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25520 : x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have j0 := eq22974 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22974
  have eq25905 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25520
       grind)
    | exact superpose eq25520 eq16
    | exact resolve eq16 eq25520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25520
  have eq25917 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq25905
       have r₂ := eq22 x
       grind)
    | exact resolve eq25905 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25905
  have eq25925 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq246
       have i₂ := eq25917
       grind)
    | exact superpose eq25917 eq246
    | exact resolve eq246 eq25917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq25917
  have eq25936 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25925
  have eq25945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25936
       have i₂ := eq22717
       grind)
    | exact superpose eq22717 eq25936
    | exact resolve eq25936 eq22717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22717 eq25936
  have eq25949 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq25945
       have r₂ := eq16
       grind)
    | exact resolve eq25945 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25945
  have eq26476 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25949
       grind)
    | exact superpose eq25949 eq16
    | exact resolve eq16 eq25949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26477 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25949
       grind)
    | exact superpose eq25949 eq10
    | exact resolve eq10 eq25949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25949
  have eq26615 : x = y := by
    first
    | (have i₁ := eq26477
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26477
    | exact resolve eq26477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26477
  have eq26616 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq26476
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq26476
    | exact resolve eq26476 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26476
  have eq26622 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq26616
       have i₂ := eq26615
       grind)
    | exact superpose eq26615 eq26616
    | exact resolve eq26616 eq26615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26615 eq26616
  have eq26623 : False := by grind
  exact eq26623
