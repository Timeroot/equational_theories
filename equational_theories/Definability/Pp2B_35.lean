import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxy_pxx_pyx_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X2 X2) (M.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 (M.op (M.op X2 X2) (M.op X3 X0))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq35 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X0)) X0) = X2 ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X2 : G, X0 = X2 ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq35 X0 x X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq35
    | (have j0 := eq35 X0 x X2
       grind)
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq40 : ∀ X0 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have j0 := eq39 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq43 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 (M.op X1 X0) X1
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq25 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X2) (M.op (σ (M.op X0 X0)) (M.op X3 X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X2 X1 (σ X0) X3
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (M.op X0 (M.op X2 X2)) X1 (M.op X2 X2) (M.op X3 X3)
       have i₂ := eq24 (M.op X2 X2) X2 X3 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq118 : ∀ X2 X3 : G, (M.op X2 X2) = (M.op X3 X3) := by
    intro X2 X3
    first
    | (have i₁ := eq103 x x X3 X2
       have i₂ := eq9 (M.op X3 X3) x x
       grind)
    | exact superpose eq9 eq103
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq123 : ∀ X0 X2 X3 : G, (M.op X2 (M.op (σ (M.op X0 X0)) (M.op X3 X2))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq96 X0 x X2 X3
       have i₂ := eq51 x X2
       grind)
    | exact superpose eq51 eq96
    | exact resolve eq96 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq263 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq43
    | (have j0 := eq43 X0 X1
       have j1 := eq40 (σ (M.op X0 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq43 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq43
  have eq595 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq46 (M.op X1 X1) X0
       have i₂ := eq51 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq51 eq46
    | exact resolve eq46 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq648 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq118 (σ X1) X0
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq118 X0 (σ X1)
       grind)
    | exact superpose eq118 eq22
    | exact resolve eq22 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq118
  have eq1402 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X1)) X1 (σ (M.op X2 X2))
       have i₂ := eq123 X2 (M.op X1 X1) X0
       grind)
    | exact superpose eq123 eq9
    | exact resolve eq9 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq1413 : ∀ X0 X2 : G, (M.op X0 (σ (M.op X2 X2))) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq1402 X0 x X2
       have i₂ := eq595 X0 x
       grind)
    | exact superpose eq595 eq1402
    | exact resolve eq1402 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq1402
  have eq3736 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq263 x y
       grind)
    | exact superpose eq263 eq16
    | (have j1 := eq263 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq263 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq263 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq263 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq3780 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3736
  have eq5974 : (σ x) = (M.op (σ y) (σ (M.op x x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46 (σ y) (σ x)
       have i₂ := eq3780
       grind)
    | exact superpose eq3780 eq46
    | exact resolve eq46 eq3780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq3780
  have eq6007 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5974
       have i₂ := eq1413 (σ y) x
       grind)
    | exact superpose eq1413 eq5974
    | exact resolve eq5974 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413 eq5974
  have eq6008 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6007
  have eq7873 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6008
       grind)
    | exact superpose eq6008 eq10
    | exact resolve eq10 eq6008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6008
  have eq7914 : x = y ∨ x = y := by
    first
    | (have i₁ := eq7873
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7873
    | exact resolve eq7873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7873
  have eq7915 : x = y := by grind
  clear eq7914
  have eq10410 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7915
       grind)
    | exact superpose eq7915 eq16
    | exact resolve eq16 eq7915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7915
  have eq10411 : False := by grind
  exact eq10411

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pxy_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
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
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ x) (σ y)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X0) X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X1) (M.op (M.op X1 X1) X0)
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq86 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq60 (M.op X0 X0) X1
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq134 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq130
  have eq135 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq134
  have eq177 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
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
  have eq185 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq177
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq177
    | exact resolve eq177 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq186 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq185
    | exact resolve eq185 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq210 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq254 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq135
       grind)
    | exact superpose eq135 eq16
    | exact resolve eq16 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq344 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq210
       have i₂ := eq86 X0 sF2
       grind)
    | (have i₁ := eq210
       have i₂ := eq86 sF2 x
       grind)
    | exact superpose eq86 eq210
    | exact resolve eq210 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq210
  have eq378 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq61
    | exact resolve eq61 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq61
  have eq9901 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq186 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq9902 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq9901
    | exact resolve eq9901 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9901
  have eq9913 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq9902
       have r₂ := eq28
       grind)
    | exact resolve eq9902 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9902
  have eq9918 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq9913 eq60
    | exact resolve eq60 eq9913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq9913
  have eq9924 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq9918
    | exact resolve eq9918 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9918
  have eq9927 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq9924
       grind)
    | exact superpose eq9924 eq56
    | exact resolve eq56 eq9924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9924
  have eq10076 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq378 y X0
       have i₂ := eq9927
       grind)
    | exact superpose eq9927 eq378
    | exact resolve eq378 eq9927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq9927
  have eq10099 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10076 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10076
    | (have j0 := eq10076 X0
       grind)
    | exact resolve eq10076 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10076
  have eq11049 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq10099 eq27
    | (have j1 := eq10099 (σ y)
       grind)
    | exact resolve eq27 eq10099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10099
  have eq11083 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11049
  have eq11228 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11083 eq28
    | exact resolve eq28 eq11083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11230 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11083 eq67
    | exact resolve eq67 eq11083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq11083
  have eq11366 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11230 eq254
    | exact resolve eq254 eq11230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq11230
  have eq11422 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq11366
    | exact resolve eq11366 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11366
  have eq12902 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq11422
       grind)
    | exact superpose eq11422 eq56
    | exact resolve eq56 eq11422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq11422
  have eq12908 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12902
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12902
    | exact resolve eq12902 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12902
  have eq12960 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12908 eq30
    | exact resolve eq30 eq12908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12908
  have eq13084 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq12960
    | exact resolve eq12960 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12960
  have eq13085 : y = (M.op x y) ∨ x = y := by grind
  clear eq13084
  have eq13107 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq13085 eq21
    | exact resolve eq21 eq13085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13213 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13107
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13107
    | exact resolve eq13107 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13107
  have eq13321 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq13213 eq11228
    | (have r₁ := eq11228
       have r₂ := eq13213
       grind)
    | exact resolve eq11228 eq13213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11228 eq13213
  have eq13334 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq13321
  have eq13335 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq13334
  have eq13542 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq13335 eq29
    | exact resolve eq29 eq13335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13335
  have eq13683 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq13542
    | exact resolve eq13542 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq13542
  have eq13953 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq13683 eq13085
    | exact resolve eq13085 eq13683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13085 eq13683
  have eq13954 : x = y := by grind
  clear eq13953
  have eq14032 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq13954
       grind)
    | exact superpose eq13954 eq19
    | exact resolve eq19 eq13954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq14033 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq13954
       grind)
    | exact superpose eq13954 eq25
    | exact resolve eq25 eq13954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq13954
  have eq14137 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14033
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14033
    | exact resolve eq14033 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14033
  have eq14358 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14137 eq27
    | exact resolve eq27 eq14137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14137
  have eq15185 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq14358 eq344
    | exact resolve eq344 eq14358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq14358
  have eq15214 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq15185
       have i₂ := eq14032
       grind)
    | exact superpose eq14032 eq15185
    | exact resolve eq15185 eq14032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14032 eq15185
  have eq15399 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15214 eq15
    | exact resolve eq15 eq15214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15214
  have eq15438 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq15399
    | exact resolve eq15399 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq15399
  have eq15449 : False := by grind
  exact eq15449

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxy_pxx_pyx_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ x) (σ y)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X0) X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X1) (M.op (M.op X1 X1) X0)
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq86 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq60 (M.op X0 X0) X1
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq211 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq217 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq129
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq129
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq226 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq217
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq217
    | exact resolve eq217 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq227 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq226
    | exact resolve eq226 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq228 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq227
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq227
    | exact resolve eq227 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq344 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq211
       have i₂ := eq86 X0 sF2
       grind)
    | (have i₁ := eq211
       have i₂ := eq86 sF2 x
       grind)
    | exact superpose eq86 eq211
    | exact resolve eq211 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq211
  have eq379 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq61
    | exact resolve eq61 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq61
  have eq873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq228 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq874 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq873
    | exact resolve eq873 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq877 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq874
       have r₂ := eq28
       grind)
    | exact resolve eq874 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq879 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq877
    | exact resolve eq877 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq883 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq879 eq58
    | exact resolve eq58 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq879
  have eq907 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq883 eq344
    | exact resolve eq344 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq916 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq907
    | exact resolve eq907 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq1393 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq60 x x
       have i₂ := eq916
       grind)
    | exact superpose eq916 eq60
    | exact resolve eq60 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq916
  have eq1400 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1393
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1393
    | exact resolve eq1393 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1401 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1400
  have eq1407 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1401 eq30
    | exact resolve eq30 eq1401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1401
  have eq1429 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1407
    | exact resolve eq1407 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1407
  have eq1430 : x = (M.op x y) ∨ x = y := by grind
  clear eq1429
  have eq1485 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1430 eq21
    | exact resolve eq21 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1487 : y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq1430 eq57
    | exact resolve eq57 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1430
  have eq1509 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1485
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1485
    | exact resolve eq1485 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485
  have eq1556 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq379 x X0
       have i₂ := eq1487
       grind)
    | exact superpose eq1487 eq379
    | exact resolve eq379 eq1487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq1487
  have eq1567 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1556 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1556
    | (have j0 := eq1556 X0
       grind)
    | exact resolve eq1556 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556
  have eq2092 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq67 eq1567
    | exact resolve eq1567 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq1567
  have eq2130 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq2092 eq28
    | exact resolve eq28 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092
  have eq2139 : x = y := by
    first
    | (have r₁ := eq2130
       have r₂ := eq1509
       grind)
    | exact resolve eq2130 eq1509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509 eq2130
  have eq2199 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2139
       grind)
    | exact superpose eq2139 eq19
    | exact resolve eq19 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2200 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2139
       grind)
    | exact superpose eq2139 eq25
    | exact resolve eq25 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2139
  have eq2224 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2200
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2200
    | exact resolve eq2200 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2200
  have eq2229 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2224 eq27
    | exact resolve eq27 eq2224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2224
  have eq2695 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2229 eq344
    | exact resolve eq344 eq2229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq2229
  have eq2705 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2695
       have i₂ := eq2199
       grind)
    | exact superpose eq2199 eq2695
    | exact resolve eq2695 eq2199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199 eq2695
  have eq2737 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2705 eq15
    | exact resolve eq15 eq2705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705
  have eq2774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq2737
    | exact resolve eq2737 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2737
  have eq2785 : False := by grind
  exact eq2785

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pxy_pyx_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq43 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (M.op X1 X0) X1
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq43
    | exact resolve eq43 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq43 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq45 (M.op X0 X0) X1
       grind)
    | exact superpose eq45 eq9
    | exact resolve eq9 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (M.op X1 X1) X0
       have i₂ := eq48 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq48 eq45
    | exact resolve eq45 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq93 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq93
    | (have j0 := eq93 X0 X1
       grind)
    | exact resolve eq93 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq128 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq63
    | exact resolve eq63 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq130 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq54
    | exact resolve eq54 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq131 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq48
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq276 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 (σ (M.op X1 X1))
       have i₂ := eq128 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq128 eq131
    | exact resolve eq131 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq131
  have eq314 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq95 x y
       grind)
    | exact superpose eq95 eq16
    | (have j1 := eq95 x (M.op x x)
       grind)
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq373 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq130 X1 X0
       grind)
    | exact superpose eq130 eq10
    | exact resolve eq10 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4349 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq314
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq314
    | (have j1 := eq14 (M.op x x) x
       grind)
    | (have r₁ := eq314
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq314
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq314 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq4350 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq4349
  have eq30845 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4350
       grind)
    | exact superpose eq4350 eq16
    | exact resolve eq16 eq4350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4350
  have eq30846 : (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq30845
       have r₂ := eq130 x (σ x)
       grind)
    | exact resolve eq30845 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30845
  have eq315680 : y = (τ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30846
       grind)
    | exact superpose eq30846 eq10
    | exact resolve eq10 eq30846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30846
  have eq315753 : x = y ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq315680
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq315680
    | exact resolve eq315680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315680
  have eq315755 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq315753
       grind)
    | exact superpose eq315753 eq16
    | exact resolve eq16 eq315753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315753
  have eq315756 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq315755
       have r₂ := eq130 x (σ x)
       grind)
    | exact resolve eq315755 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq315755
  have eq315914 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq315756
       grind)
    | exact superpose eq315756 eq10
    | exact resolve eq10 eq315756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315756
  have eq316003 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq315914
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq315914
    | exact resolve eq315914 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315914
  have eq316004 : x = (M.op x x) := by grind
  clear eq316003
  have eq316702 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48 x X0
       have i₂ := eq316004
       grind)
    | exact superpose eq316004 eq48
    | exact resolve eq48 eq316004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq316720 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq276 x X0
       have i₂ := eq316004
       grind)
    | exact superpose eq316004 eq276
    | exact resolve eq276 eq316004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq316724 : ∀ X0 : G, (M.op X0 X0) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq373 x X0
       have i₂ := eq316004
       grind)
    | exact superpose eq316004 eq373
    | exact resolve eq373 eq316004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq316004
  have eq317266 : (σ x) = (σ (τ x)) := by
    first
    | (have i₁ := eq316720 x
       have i₂ := eq316724 x
       grind)
    | exact superpose eq316724 eq316720
    | exact resolve eq316720 eq316724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316720 eq316724
  have eq317320 : x = (σ x) := by
    first
    | (have i₁ := eq317266
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq317266
    | exact resolve eq317266 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317266
  have eq317360 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq317320
       grind)
    | exact superpose eq317320 eq16
    | exact resolve eq16 eq317320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317320
  have eq317441 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq317360
       have i₂ := eq316702 (σ y)
       grind)
    | exact superpose eq316702 eq317360
    | exact resolve eq317360 eq316702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317360
  have eq317462 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq317441
       have i₂ := eq316702 y
       grind)
    | exact superpose eq316702 eq317441
    | exact resolve eq317441 eq316702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316702 eq317441
  have eq317463 : False := by grind
  exact eq317463

/-- `Equation2865`: `x = ((x ◇ (y ◇ x)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_pyy_pxy_pyx_pxy_Equation2865 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2865 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2865.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) ≠ (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq12 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq77 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq77
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq80
    | exact resolve eq80 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq87 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq93 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq87 (τ X0)
       grind)
    | exact superpose eq87 eq18
    | exact resolve eq18 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq94 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq98 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq94 X0
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq94
    | exact resolve eq94 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq130 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq130 (σ X0) (σ X1)
       grind)
    | exact superpose eq130 eq15
    | (have j1 := eq130 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq230 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq230
    | (have j0 := eq230 X0 X1
       grind)
    | exact resolve eq230 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq258 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq245 X0 X1
       have i₂ := eq87 X1
       grind)
    | exact superpose eq87 eq245
    | (have j0 := eq245 X0 X1
       grind)
    | exact resolve eq245 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq266 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq258 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq258
    | (have j0 := eq258 X0 X1
       grind)
    | exact resolve eq258 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq268 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq266 X0 X1
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq266
    | (have j0 := eq266 X0 X1
       grind)
    | exact resolve eq266 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq443 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq268 x y
       grind)
    | exact superpose eq268 eq16
    | (have j1 := eq268 x y
       grind)
    | exact resolve eq16 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq461 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq443
       grind)
    | exact superpose eq443 eq10
    | exact resolve eq10 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq492 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq461
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq461
    | exact resolve eq461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq741 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq742 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 X1
       have i₂ := eq87 X1
       grind)
    | exact superpose eq87 eq741
    | (have j0 := eq741 X0 X1
       grind)
    | exact resolve eq741 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq743 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq742 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq742
    | (have j0 := eq742 X0 X1
       grind)
    | exact resolve eq742 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq742
  have eq744 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq743 X0 X1
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq743
    | (have j0 := eq743 X0 X1
       grind)
    | exact resolve eq743 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq743
  have eq1130 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq744 X0 X1
       grind)
    | (have i₁ := eq32 X1 X0
       have i₂ := eq744 X0 X1
       grind)
    | exact superpose eq744 eq32
    | (have j1 := eq744 X1 X0
       grind)
    | (have r₁ := eq32 X0 X1
       have r₂ := eq744 X0 X1
       grind)
    | (have r₁ := eq32 X1 X0
       have r₂ := eq744 X0 X1
       grind)
    | exact resolve eq32 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq744
  have eq1145 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1130 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1146 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1145 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq1187 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1146 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1146
    | (have j0 := eq1146 (τ X0) X1
       grind)
    | exact resolve eq1146 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1202 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) ≠ (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1146 x y
       grind)
    | exact superpose eq1146 eq16
    | (have j1 := eq1146 x y
       grind)
    | exact resolve eq16 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1233 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1187 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq1187
    | (have j0 := eq1187 X0 X1
       grind)
    | exact resolve eq1187 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1187
  have eq1240 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1233 X0 X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq1233
    | (have j0 := eq1233 X0 X1
       grind)
    | exact resolve eq1233 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq1392 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq492
       have i₂ := eq130 x y
       grind)
    | exact superpose eq130 eq492
    | (have j1 := eq130 x y
       grind)
    | exact resolve eq492 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq492
  have eq1398 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq1392
  have eq1399 : (M.op x x) = (M.op y y) := by grind
  clear eq1398
  have eq1466 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) ≠ (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1240 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1240
    | (have j0 := eq1240 X1 (τ X0)
       grind)
    | exact resolve eq1240 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq1526 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1466 X0 X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq1466
    | (have j0 := eq1466 X0 X1
       grind)
    | (have r₁ := eq1466 X0 X0
       have r₂ := eq98 X0
       grind)
    | exact resolve eq1466 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq1466
  have eq1705 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq1202
       have i₂ := eq1399
       grind)
    | exact superpose eq1399 eq1202
    | exact resolve eq1202 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1706 : (σ (M.op x y)) ≠ (σ (k y x)) := by grind
  clear eq1705
  have eq1966 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) ≠ (M.op y y) := by
    first
    | (have i₁ := eq1706
       have i₂ := eq1526 x y
       grind)
    | exact superpose eq1526 eq1706
    | (have j1 := eq1526 x y
       grind)
    | exact resolve eq1706 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526 eq1706
  have eq1967 : (M.op x x) ≠ (M.op y y) := by grind
  clear eq1966
  have eq1968 : False := by grind
  exact eq1968

/-- `Equation2883`: `x = ((x ◇ (y ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_y_pxy_Equation2883 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2883 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2883.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X1) (M.op (M.op X0 (M.op X2 X3)) X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 (M.op X2 X3)) X0) X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X0) X1 X2
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : y ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
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
  have eq64 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k y x) := by
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
  have eq76 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq94 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq134 eq16
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X1) (M.op (M.op X0 (M.op x y)) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq613 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ y) (M.op X0 X1)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X4)) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) X0) X3 X4
       have i₂ := eq52 X0 (M.op X0 (M.op X1 X2)) X1 X2
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op (M.op X0 X2) X0)) X1) (M.op X0 (M.op (M.op X0 X2) X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op (M.op X0 X2) X0) X1 (M.op X2 (M.op x x)) X2
       have i₂ := eq52 X2 X0 x x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq848 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq854 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq848 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq855 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq849 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq849 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq849 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq849 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq856 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq854 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq854 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq854 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq854 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq865 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq855 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq855
    | (have j0 := eq855 X0 X1
       grind)
    | exact resolve eq855 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq866 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq856 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq856
    | (have j0 := eq856 X0 X1
       grind)
    | exact resolve eq856 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq1023 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ y) (M.op x y)) (σ y))) := by
    first
    | exact superpose eq26 eq214
    | (have j0 := eq214 (σ y) (σ x)
       grind)
    | exact resolve eq214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1059 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq1023 eq14
    | exact resolve eq14 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1145 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1059 eq214
    | exact resolve eq214 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1223 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (M.op (M.op X0 (M.op (M.op X0 (σ x)) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq613 eq53
    | exact resolve eq53 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3875 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op X0 (M.op (M.op X0 (M.op x y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq214 X0 (M.op X0 (M.op (M.op X0 X1) X0))
       have i₂ := eq625 X0 X0 X1
       grind)
    | exact superpose eq625 eq214
    | exact resolve eq214 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq4720 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq94 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq94
    | (have j0 := eq94 x
       grind)
    | exact resolve eq94 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq4744 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4720
  have eq4749 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4744
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq4744
    | exact resolve eq4744 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq4744
  have eq4767 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq4749
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq4749 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4749
  have eq4774 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq4767 eq49
    | exact resolve eq49 eq4767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq4767
  have eq5254 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq135
    | (have j0 := eq135 (M.op x y)
       grind)
    | exact resolve eq135 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq5276 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5254
  have eq5279 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134 eq5276
    | exact resolve eq5276 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq5276
  have eq5311 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq5279
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5279 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5279
  have eq5350 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5311 eq157
    | exact resolve eq157 eq5311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq5311
  have eq9215 : ∀ X2 X3 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (σ x) (M.op (M.op (σ x) (M.op X2 X3)) (σ x))) := by
    intro X2 X3
    first
    | exact superpose eq613 eq618
    | exact resolve eq618 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq618
  have eq17915 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17922 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq17915
    | exact resolve eq17915 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17915
  have eq17933 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq17922
       have r₂ := eq27
       grind)
    | exact resolve eq17922 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17922
  have eq17935 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq17933
    | exact resolve eq17933 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17933
  have eq17939 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq17935 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq17935
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq17935
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq17935
       grind)
    | exact resolve eq12 eq17935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17935
  have eq17980 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq17939
  have eq17992 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq17980
    | exact resolve eq17980 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17980
  have eq17993 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq17992
  have eq18330 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq17993 eq57
    | exact resolve eq57 eq17993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq18331 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq17993 eq116
    | exact resolve eq116 eq17993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17993
  have eq18349 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18331
  have eq18358 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq18330
    | exact resolve eq18330 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18330
  have eq18363 : x ≠ x ∨ y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18349
       grind)
    | exact superpose eq18349 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq18349
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18349
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq18349
       grind)
    | exact resolve eq12 eq18349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18364 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18349
       grind)
    | exact superpose eq18349 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18349
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18349
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18349
       grind)
    | exact resolve eq13 eq18349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18349
  have eq18404 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18364
  have eq18405 : y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18363
  have eq18416 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18404
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18404
    | exact resolve eq18404 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18404
  have eq18417 : y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18405
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18405
    | exact resolve eq18405 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18405
  have eq18418 : y = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18417
  have eq18555 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq18416
       grind)
    | exact superpose eq18416 eq72
    | exact resolve eq72 eq18416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18416
  have eq18581 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq18555
    | exact resolve eq18555 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18555
  have eq18776 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq852 x y
       have i₂ := eq18418
       grind)
    | exact superpose eq18418 eq852
    | (have j0 := eq852 x y
       grind)
    | exact resolve eq852 eq18418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18418
  have eq18781 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18776
  have eq18786 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18781
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18781
    | exact resolve eq18781 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18781
  have eq18799 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18786
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18786
    | exact resolve eq18786 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18786
  have eq18807 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18799
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18799
    | exact resolve eq18799 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18799
  have eq18813 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18807
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18807
    | exact resolve eq18807 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18807
  have eq18818 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18813
    | exact resolve eq18813 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18813
  have eq18819 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq18818
  have eq19041 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18819 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18819
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18819
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18819
       grind)
    | exact resolve eq13 eq18819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18819
  have eq19081 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq19041
  have eq19093 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq19081
    | exact resolve eq19081 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19081
  have eq19241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19093 eq18581
    | exact resolve eq18581 eq19093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18581 eq19093
  have eq19249 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19241
  have eq19251 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19249
       have r₂ := eq27
       grind)
    | exact resolve eq19249 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19249
  have eq19254 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) X0) (σ x)) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19251 eq51
    | exact resolve eq51 eq19251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19355 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq19254
    | (have j0 := eq19254 (σ x)
       grind)
    | exact resolve eq19254 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19254
  have eq19416 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19251 eq19355
    | exact resolve eq19355 eq19251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19251 eq19355
  have eq19472 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq19416
  have eq19542 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18358
       grind)
    | exact superpose eq18358 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18358
  have eq19552 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19542
  have eq19560 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19552
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19552
    | exact resolve eq19552 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19552
  have eq19561 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19560
  have eq19592 : x ≠ x ∨ y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19561
       grind)
    | exact superpose eq19561 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq19561
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19561
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq19561
       grind)
    | exact resolve eq12 eq19561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19593 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19561
       grind)
    | exact superpose eq19561 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19561
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19561
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19561
       grind)
    | exact resolve eq13 eq19561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19561
  have eq19633 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19593
  have eq19634 : y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19592
  have eq19645 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19633
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19633
    | exact resolve eq19633 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19633
  have eq19646 : y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19634
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19634
    | exact resolve eq19634 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19634
  have eq19647 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19646
  have eq19652 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq19645
       grind)
    | exact superpose eq19645 eq72
    | exact resolve eq72 eq19645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19645
  have eq19678 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq19652
    | exact resolve eq19652 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19652
  have eq19739 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq852 x y
       have i₂ := eq19647
       grind)
    | exact superpose eq19647 eq852
    | (have j0 := eq852 x y
       grind)
    | exact resolve eq852 eq19647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19741 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq866 x y
       have i₂ := eq19647
       grind)
    | exact superpose eq19647 eq866
    | (have j0 := eq866 x y
       grind)
    | exact resolve eq866 eq19647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866 eq19647
  have eq19742 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19741
  have eq19744 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19739
  have eq19747 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19742
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq19742
    | exact resolve eq19742 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19742
  have eq19749 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19744
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19744
    | exact resolve eq19744 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19744
  have eq19760 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19747
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19747
    | exact resolve eq19747 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19747
  have eq19762 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19749
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19749
    | exact resolve eq19749 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19749
  have eq19768 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19760
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19760
    | exact resolve eq19760 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19760
  have eq19770 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19762
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19762
    | exact resolve eq19762 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19762
  have eq19774 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19768
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19768
    | exact resolve eq19768 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19768
  have eq19776 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19770
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19770
    | exact resolve eq19770 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19770
  have eq19780 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19774
       have r₂ := eq76
       grind)
    | exact resolve eq19774 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq19774
  have eq19781 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq19776
    | exact resolve eq19776 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19776
  have eq19782 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19781
  have eq19882 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19782 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19782
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19782
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19782
       grind)
    | exact resolve eq13 eq19782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19782
  have eq19922 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19882
  have eq19936 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq19922
    | exact resolve eq19922 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19922
  have eq19953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19936 eq19678
    | exact resolve eq19678 eq19936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19678 eq19936
  have eq19961 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19953
  have eq19965 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19961
       have r₂ := eq27
       grind)
    | exact resolve eq19961 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19961
  have eq19968 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19965 eq27
    | exact resolve eq27 eq19965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19969 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) X0) (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19965 eq51
    | exact resolve eq51 eq19965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq19970 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19965 eq64
    | (have r₁ := eq64
       have r₂ := eq19965
       grind)
    | exact resolve eq64 eq19965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq19994 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq19970
  have eq20004 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19994 eq116
    | exact resolve eq116 eq19994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq20024 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq20004
  have eq20081 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq19969
    | (have j0 := eq19969 (σ x)
       grind)
    | exact resolve eq19969 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19969
  have eq20142 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19965 eq20081
    | exact resolve eq20081 eq19965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20081
  have eq20200 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq20142
  have eq20273 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19780 eq82
    | exact resolve eq82 eq19780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq20315 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq20273
    | exact resolve eq20273 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20273
  have eq20321 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20315 eq19472
    | exact resolve eq19472 eq20315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19472
  have eq20371 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq20321
  have eq20388 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq20371
       have r₂ := eq19968
       grind)
    | exact resolve eq20371 eq19968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20371
  have eq20434 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20024 eq20315
    | exact resolve eq20315 eq20024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20024 eq20315
  have eq20478 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq20434
  have eq20492 : x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq20478
       have r₂ := eq75
       grind)
    | exact resolve eq20478 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20478
  have eq20576 : (τ (σ x)) = (k x x) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq20388 eq4774
    | exact resolve eq4774 eq20388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4774 eq20388
  have eq20628 : x = (k y x) ∨ y = (M.op x y) ∨ x = (k x x) := by
    first
    | exact superpose eq28 eq20576
    | exact resolve eq20576 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq20576
  have eq20643 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq20492
       grind)
    | exact superpose eq20492 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq20492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20492
  have eq20653 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq20643
  have eq20661 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq20653
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20653
    | exact resolve eq20653 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20653
  have eq20708 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq20661
       grind)
    | exact superpose eq20661 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20661
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20661
       grind)
    | exact resolve eq13 eq20661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20661
  have eq20748 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq20708
  have eq20760 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq20748
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20748
    | exact resolve eq20748 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20748
  have eq20769 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq20760
       grind)
    | exact superpose eq20760 eq72
    | exact resolve eq72 eq20760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20760
  have eq20801 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq20769
    | exact resolve eq20769 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20769
  have eq20896 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20801 eq19780
    | exact resolve eq19780 eq20801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19780
  have eq20908 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq20896
  have eq20988 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20908 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20908
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20908
       grind)
    | exact resolve eq13 eq20908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20908
  have eq21028 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq20988
  have eq21046 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq21028
    | exact resolve eq21028 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21028
  have eq25121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21046 eq20801
    | exact resolve eq20801 eq21046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20801 eq21046
  have eq25131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq25121
  have eq25140 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq25131
       have r₂ := eq27
       grind)
    | exact resolve eq25131 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25131
  have eq25145 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25140 eq26
    | exact resolve eq26 eq25140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25147 : ∀ X0 : G, (σ (k x X0)) = (k (σ (M.op x y)) (σ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25140 eq35
    | exact resolve eq35 eq25140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq25148 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25140 eq39
    | exact resolve eq39 eq25140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq25349 : ∀ X0 : G, (σ (k X0 x)) = (σ (k X0 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41 eq25148
    | exact resolve eq25148 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq25148
  have eq25350 : ∀ X0 : G, (σ (k x X0)) = (σ (k (M.op x y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37 eq25147
    | exact resolve eq25147 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq25147
  have eq31442 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (σ (k X0 x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25349 eq16
    | exact resolve eq16 eq25349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25349
  have eq31533 : ∀ X0 : G, (k X0 x) = (k X0 (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq31442 X0
       have i₂ := eq16 (k X0 x)
       grind)
    | exact superpose eq16 eq31442
    | exact resolve eq31442 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31442
  have eq53648 : (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (σ x) (M.op (M.op (σ x) (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq9215 x x
       have i₂ := eq3875 sF2 (M.op x x)
       grind)
    | (have i₁ := eq9215 x y
       have i₂ := eq3875 sF2 x
       grind)
    | exact superpose eq3875 eq9215
    | (have j0 := eq9215 x y
       have j1 := eq3875 (σ x) (σ y)
       grind)
    | exact resolve eq9215 eq3875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3875 eq9215
  have eq54055 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq20628
       grind)
    | exact superpose eq20628 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq20628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20628
  have eq54065 : x = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k x x) := by grind
  clear eq54055
  have eq54079 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq54065
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54065
    | exact resolve eq54065 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54065
  have eq54080 : x = (k x x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq54079
  have eq54321 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq54080
       grind)
    | exact superpose eq54080 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq54080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54080
  have eq54334 : x = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq54321
  have eq54618 : x ≠ x ∨ y = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq54334
       grind)
    | exact superpose eq54334 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq54334
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq54334
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq54334
       grind)
    | exact resolve eq12 eq54334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54334
  have eq54669 : y = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq54618
  have eq54698 : y = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq54669
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54669
    | exact resolve eq54669 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54669
  have eq54699 : y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq54698
  have eq55189 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq54699
       grind)
    | exact superpose eq54699 eq44
    | exact resolve eq44 eq54699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54699
  have eq55231 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq55189
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq55189
    | exact resolve eq55189 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55189
  have eq55397 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq55231 eq19994
    | exact resolve eq19994 eq55231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19994 eq55231
  have eq55429 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq55397
  have eq56101 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq55429 eq20200
    | exact resolve eq20200 eq55429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20200
  have eq56172 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq56101
  have eq57672 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq56172 eq55429
    | exact resolve eq55429 eq56172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55429 eq56172
  have eq57731 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq57672
  have eq57871 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq57731
       grind)
    | exact superpose eq57731 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq57731
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq57731
       grind)
    | exact resolve eq13 eq57731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57731
  have eq57921 : x = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq57871
  have eq57955 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq865 x x
       have i₂ := eq57921
       grind)
    | exact superpose eq57921 eq865
    | (have j0 := eq865 x x
       grind)
    | exact resolve eq865 eq57921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57921
  have eq57956 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq57955
  have eq57957 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq57956
  have eq57967 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57957
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq57957
    | exact resolve eq57957 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57957
  have eq58375 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25140 eq57967
    | exact resolve eq57967 eq25140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57967
  have eq58449 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq58375
  have eq58480 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq58449
       have r₂ := eq19968
       grind)
    | exact resolve eq58449 eq19968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19968 eq58449
  have eq58487 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq58480 eq5350
    | exact resolve eq5350 eq58480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5350
  have eq58495 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ (M.op x y))) X0) (σ (M.op x y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq58480 eq14
    | exact resolve eq14 eq58480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58480
  have eq58570 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq58487
    | exact resolve eq58487 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq58487
  have eq58604 : (M.op x y) = (k (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq58570 eq31533
    | exact resolve eq31533 eq58570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31533
  have eq58611 : (σ (M.op x y)) = (σ (k x (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq58570 eq25350
    | exact resolve eq25350 eq58570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25350 eq58570
  have eq58631 : (σ (M.op x y)) = (σ (k x (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq58611
  have eq58635 : (M.op x y) = (k (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq58604
  have eq58652 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq45 eq58631
    | exact resolve eq58631 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq58631
  have eq58666 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq58652
    | exact resolve eq58652 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58652
  have eq59659 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq58635 eq865
    | (have j0 := eq865 (M.op x y) x
       grind)
    | exact resolve eq865 eq58635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58635
  have eq59661 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq59659
  have eq59672 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq59661
    | exact resolve eq59661 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59661
  have eq59688 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq59672
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq59672
    | exact resolve eq59672 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59672
  have eq59697 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq59688
       have r₂ := eq25140
       grind)
    | exact resolve eq59688 eq25140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59688
  have eq59704 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq59697
    | exact resolve eq59697 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59697
  have eq59710 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq59704
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq59704
    | exact resolve eq59704 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59704
  have eq63155 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq59710 eq13
    | (have j0 := eq13 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq59710
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq59710
       grind)
    | exact resolve eq13 eq59710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63206 : (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq63155
  have eq73434 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq63206 eq58666
    | exact resolve eq58666 eq63206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58666 eq63206
  have eq73452 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq73434
  have eq105119 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq59710 eq58495
    | exact resolve eq58495 eq59710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58495 eq59710
  have eq105197 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq105119
  have eq105410 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq105197 eq1223
    | exact resolve eq1223 eq105197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223 eq105197
  have eq105677 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73452 eq105410
    | exact resolve eq105410 eq73452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73452 eq105410
  have eq105757 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq105677
  have eq105801 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19965 eq105757
    | exact resolve eq105757 eq19965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19965 eq105757
  have eq105861 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq105801
  have eq105886 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq105861 eq25145
    | exact resolve eq25145 eq105861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25145 eq105861
  have eq105945 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq105886
  have eq105970 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq105945 eq27
    | exact resolve eq27 eq105945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105945
  have eq106036 : y = (M.op x y) := by
    first
    | (have r₁ := eq105970
       have r₂ := eq25140
       grind)
    | exact resolve eq105970 eq25140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25140 eq105970
  have eq106040 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq106036 eq20
    | exact resolve eq20 eq106036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq106044 : y ≠ y ∨ (k x y) = (M.op y x) := by
    first
    | exact superpose eq106036 eq63
    | (have r₁ := eq63
       have r₂ := eq106036
       grind)
    | exact resolve eq63 eq106036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq106047 : y ≠ y ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | exact superpose eq106036 eq75
    | (have r₁ := eq75
       have r₂ := eq106036
       grind)
    | exact resolve eq75 eq106036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq106202 : x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq106047
  have eq106203 : (k x y) = (M.op y x) := by grind
  clear eq106044
  have eq106315 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq106040
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq106040
    | exact resolve eq106040 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106040
  have eq106361 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq106315 eq26
    | exact resolve eq26 eq106315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq106740 : (k (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq106203
       grind)
    | exact superpose eq106203 eq44
    | exact resolve eq44 eq106203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq106203
  have eq106784 : (k (σ x) (σ (M.op x y))) = (σ (M.op y x)) := by
    first
    | exact superpose eq106315 eq106740
    | exact resolve eq106740 eq106315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106740
  have eq108502 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq852 y x
       have i₂ := eq106202
       grind)
    | exact superpose eq106202 eq852
    | (have j0 := eq852 y x
       grind)
    | exact resolve eq852 eq106202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq108503 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq865 y x
       have i₂ := eq106202
       grind)
    | exact superpose eq106202 eq865
    | (have j0 := eq865 y x
       grind)
    | exact resolve eq865 eq106202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq106202
  have eq108506 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq108503
  have eq108507 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq108502
  have eq108511 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq108506
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq108506
    | exact resolve eq108506 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108506
  have eq108512 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq108507
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq108507
    | exact resolve eq108507 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108507
  have eq108531 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq106315 eq108511
    | exact resolve eq108511 eq106315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108511
  have eq108532 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq106315 eq108512
    | exact resolve eq108512 eq106315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108512
  have eq108548 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq108531
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq108531
    | exact resolve eq108531 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108531
  have eq108549 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq108532
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq108532
    | exact resolve eq108532 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108532
  have eq108558 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq106361 eq108548
    | exact resolve eq108548 eq106361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108548
  have eq108559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq106361 eq108549
    | exact resolve eq108549 eq106361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108549
  have eq108564 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq108558
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq108558
    | exact resolve eq108558 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108558
  have eq108565 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq108559
       have r₂ := eq27
       grind)
    | exact resolve eq108559 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108559
  have eq108570 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq106315 eq108564
    | exact resolve eq108564 eq106315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108564
  have eq108571 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq108565
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq108565
    | exact resolve eq108565 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108565
  have eq108576 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq108570
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq108570
    | exact resolve eq108570 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108570
  have eq108577 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq108571
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq108571
    | exact resolve eq108571 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108571
  have eq108582 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq106361 eq108576
    | exact resolve eq108576 eq106361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108576
  have eq108583 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq106315 eq108577
    | exact resolve eq108577 eq106315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108577
  have eq108588 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq108582
       have r₂ := eq27
       grind)
    | exact resolve eq108582 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108582
  have eq108603 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq106784
       have i₂ := eq108588
       grind)
    | exact superpose eq108588 eq106784
    | exact resolve eq106784 eq108588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106784
  have eq108611 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq108588
       grind)
    | exact superpose eq108588 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq108588
       grind)
    | exact resolve eq13 eq108588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108588
  have eq108661 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq108611
  have eq108692 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq108661
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108661
    | exact resolve eq108661 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108661
  have eq108699 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq108603
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq108603
    | exact resolve eq108603 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108603
  have eq108727 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq106036 eq108692
    | exact resolve eq108692 eq106036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108692
  have eq108882 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108699 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq108699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108699
  have eq108893 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq106361 eq108882
    | exact resolve eq108882 eq106361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108882
  have eq108894 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq108893
  have eq108909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq106361 eq108894
    | exact resolve eq108894 eq106361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108894
  have eq108922 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq108909
       have r₂ := eq27
       grind)
    | exact resolve eq108909 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108909
  have eq108948 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq108727
       grind)
    | exact superpose eq108727 eq72
    | exact resolve eq72 eq108727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq108727
  have eq109004 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq106315 eq108948
    | exact resolve eq108948 eq106315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108948
  have eq109022 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109004
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq109004
    | exact resolve eq109004 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109004
  have eq109039 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq106315 eq109022
    | exact resolve eq109022 eq106315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109022
  have eq109801 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108922 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ x)
       have r₂ := eq108922
       grind)
    | exact resolve eq13 eq108922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108922
  have eq109852 : (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq109801
  have eq109888 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq106361 eq109852
    | exact resolve eq109852 eq106361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109852
  have eq110162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109888 eq109039
    | exact resolve eq109039 eq109888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109039 eq109888
  have eq110176 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq110162
  have eq110181 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq110176
       have r₂ := eq27
       grind)
    | exact resolve eq110176 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110176
  have eq110197 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq110181 eq27
    | exact resolve eq27 eq110181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110212 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (M.op x y)) (σ x))) := by
    first
    | exact superpose eq110181 eq1145
    | exact resolve eq1145 eq110181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq110245 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq53648 eq110212
    | exact resolve eq110212 eq53648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53648 eq110212
  have eq110257 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq110181 eq110245
    | exact resolve eq110245 eq110181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110245
  have eq111510 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ (M.op x y))) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq108583 eq1059
    | exact resolve eq1059 eq108583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059 eq108583
  have eq111601 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ (M.op x y))) (M.op (σ x) (σ x))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq110181 eq111510
    | exact resolve eq111510 eq110181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111510
  have eq111636 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq106361 eq111601
    | exact resolve eq111601 eq106361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111601
  have eq111647 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq110181 eq111636
    | exact resolve eq111636 eq110181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110181 eq111636
  have eq111654 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq110257 eq111647
    | exact resolve eq111647 eq110257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111647
  have eq113040 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq111654 eq110257
    | exact resolve eq110257 eq111654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110257 eq111654
  have eq113126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq106361 eq113040
    | exact resolve eq113040 eq106361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106361 eq113040
  have eq113153 : x = (M.op y x) := by
    first
    | (have r₁ := eq113126
       have r₂ := eq27
       grind)
    | exact resolve eq113126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq113126
  have eq113192 : y = (M.op (M.op x y) (M.op (M.op x (M.op x y)) x)) := by
    first
    | (have i₁ := eq214 x y
       have i₂ := eq113153
       grind)
    | exact superpose eq113153 eq214
    | exact resolve eq214 eq113153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq113267 : y = (M.op (M.op x y) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq106036 eq113192
    | exact resolve eq113192 eq106036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113192
  have eq113305 : y = (M.op (M.op x y) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq113267
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113267
    | exact resolve eq113267 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq113267
  have eq113321 : y = (M.op y (M.op y x)) := by
    first
    | exact superpose eq106036 eq113305
    | exact resolve eq113305 eq106036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106036 eq113305
  have eq113330 : y = (M.op y x) := by
    first
    | (have i₁ := eq113321
       have i₂ := eq113153
       grind)
    | exact superpose eq113153 eq113321
    | exact resolve eq113321 eq113153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113321
  have eq113334 : x = y := by
    first
    | (have i₁ := eq113330
       have i₂ := eq113153
       grind)
    | exact superpose eq113153 eq113330
    | exact resolve eq113330 eq113153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113153 eq113330
  have eq113340 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq113334
       grind)
    | exact superpose eq113334 eq24
    | exact resolve eq24 eq113334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq113334
  have eq113673 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq106315 eq113340
    | exact resolve eq113340 eq106315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106315 eq113340
  have eq113810 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq113673
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq113673
    | exact resolve eq113673 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq113673
  have eq113872 : False := by grind
  exact eq113872

/-- `Equation2891`: `x = ((x ◇ (y ◇ z)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_x_pxy_Equation2891 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2891 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2891.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X1) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
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
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq133 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
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
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) y) x) = X0 := by
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
  have eq176 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X0 (M.op X2 X3)) X3)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (M.op (M.op X0 (M.op X2 X3)) X3) X2
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X3) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X3) X1 X2
       have i₂ := eq16 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X1 (M.op X2 X1))) X2 X1
       have i₂ := eq16 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq181 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X2) ≠ X0 ∨ (k X1 (M.op (M.op X0 (M.op X1 X2)) X2)) = (M.op X1 (M.op (M.op X0 (M.op X1 X2)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op (M.op X0 (M.op X1 X2)) X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X1 (M.op (M.op X0 (M.op X1 X2)) X2)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X1)) X1) = (M.op (M.op X0 y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op (M.op X0 (M.op sF0 x)) x)
       have i₂ := eq16 X0 sF0 x
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq175 (M.op X0 (M.op y sF0))
       have i₂ := eq16 X0 y sF0
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) X1) = (M.op (M.op X0 (σ y)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op (M.op X0 (M.op sF4 x)) x)
       have i₂ := eq16 X0 sF4 x
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq176 (M.op X0 (M.op sF3 sF4))
       have i₂ := eq16 X0 sF3 sF4
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op x y)) y) = X0 := by
    intro X0
    first
    | exact superpose eq184 eq16
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq202 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq188 eq16
    | exact resolve eq16 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq192 (M.op X0 (M.op sF0 x))
       have i₂ := eq16 X0 sF0 x
       grind)
    | exact superpose eq16 eq192
    | exact resolve eq192 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq202 (M.op X0 (M.op sF4 sF2))
       have i₂ := eq16 X0 sF4 sF2
       grind)
    | exact superpose eq16 eq202
    | exact resolve eq202 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 : G, (M.op (M.op (M.op X0 y) x) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq302 eq16
    | exact resolve eq16 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq306 eq16
    | exact resolve eq16 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (M.op y X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq310 (M.op (M.op X0 (M.op y X1)) X1)
       have i₂ := eq16 X0 y X1
       grind)
    | exact superpose eq16 eq310
    | exact resolve eq310 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq310 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq310
    | (have j0 := eq310 x
       grind)
    | exact resolve eq310 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq340 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ y) X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq320 (M.op (M.op X0 (M.op sF3 x)) x)
       have i₂ := eq16 X0 sF3 x
       grind)
    | exact superpose eq16 eq320
    | exact resolve eq320 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq320
    | (have j0 := eq320 (σ x)
       grind)
    | exact resolve eq320 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq617 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X3)) X3)) = (M.op X1 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq179 X1 X2 (M.op (M.op X0 (M.op X2 X3)) X3)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op x y)) y)) = (M.op X1 (M.op x X0)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq179
    | exact resolve eq179 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) = (M.op X1 (M.op (σ x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq176 eq179
    | exact resolve eq179 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X2 (M.op X0 X1) X1
       have i₂ := eq179 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 (M.op X1 X2)
       have i₂ := eq179 X0 X2 X1
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X2 X3))) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq179 X1 X3 (M.op (M.op X0 X2) (M.op X2 X3))
       have i₂ := eq632 X0 X2 X3
       grind)
    | exact superpose eq632 eq179
    | exact resolve eq179 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 (M.op X1 X2)) X2) X1) = X0 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (M.op (M.op X0 (M.op X1 X2)) X2) X1
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq28
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq810 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq811 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 (k X0 X1)) X1) X0) = X2 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq857 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq882 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq893 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by
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
  have eq894 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq882 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq882 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq882 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq882 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq882 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq907 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq808
       grind)
    | exact superpose eq808 eq41
    | exact resolve eq41 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq907
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq907
    | exact resolve eq907 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq910 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq908
    | exact resolve eq908 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq910 eq809
    | exact resolve eq809 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq918
       have r₂ := eq27
       grind)
    | exact resolve eq918 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq3628 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq925 eq894
    | (have r₁ := eq894
       have r₂ := eq925
       grind)
    | exact resolve eq894 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq3629 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3628
  have eq3630 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq910 eq3629
    | exact resolve eq3629 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3629
  have eq3873 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3630 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3630
       grind)
    | exact resolve eq13 eq3630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3630
  have eq3885 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq3873
  have eq3908 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq3885
    | exact resolve eq3885 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3885
  have eq3921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq910 eq3908
    | exact resolve eq3908 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910 eq3908
  have eq3926 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3921
       have r₂ := eq27
       grind)
    | exact resolve eq3921 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3921
  have eq3929 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3926 eq29
    | exact resolve eq29 eq3926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq3936 : (k (M.op x y) y) = (τ (k (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3926 eq133
    | exact resolve eq133 eq3926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq3926
  have eq3943 : (k x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq99 eq3936
    | exact resolve eq3936 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq3936
  have eq3950 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq3929
    | exact resolve eq3929 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3929
  have eq3951 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq808 eq3943
    | exact resolve eq3943 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq3943
  have eq3954 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3950
       grind)
    | exact superpose eq3950 eq18
    | exact resolve eq18 eq3950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3955 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3950
       grind)
    | exact superpose eq3950 eq24
    | exact resolve eq24 eq3950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq3958 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq3950
       grind)
    | exact superpose eq3950 eq175
    | exact resolve eq175 eq3950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3960 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op x y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq192 X0
       have i₂ := eq3950
       grind)
    | exact superpose eq3950 eq192
    | exact resolve eq192 eq3950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3962 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq893
       have i₂ := eq3950
       grind)
    | exact superpose eq3950 eq893
    | (have r₁ := eq893
       have r₂ := eq3950
       grind)
    | exact resolve eq893 eq3950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq3950
  have eq3963 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3962
  have eq3966 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3955
    | exact resolve eq3955 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3955
  have eq4218 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 (M.op X3 X4)) X4)) = (M.op X1 (M.op X0 (M.op (M.op X0 X2) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq626 (M.op (M.op X0 X2) X3) (M.op (M.op X2 (M.op X3 X4)) X4) X1
       have i₂ := eq177 X2 X0 X3 X4
       grind)
    | exact superpose eq177 eq626
    | exact resolve eq626 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4228 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X2) X3))) = (M.op X1 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4218 X0 X1 X2 X3 x
       have i₂ := eq617 X2 X1 X3 x
       grind)
    | exact superpose eq617 eq4218
    | exact resolve eq4218 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4218
  have eq4626 : ∀ X0 : G, (k (M.op (M.op X0 (M.op x y)) (M.op x y)) x) = X0 ∨ x = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3954 eq798
    | (have j0 := eq798 (k (M.op (M.op X0 (M.op x y)) (M.op x y)) x) X0 x
       grind)
    | exact resolve eq798 eq3954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq5489 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 X4)) X4)) = (M.op (M.op X1 X3) (M.op X0 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq178 X1 (M.op X0 X2) X3 (M.op (M.op X2 (M.op X3 X4)) X4)
       have i₂ := eq177 X2 X0 X3 X4
       grind)
    | exact superpose eq177 eq178
    | exact resolve eq178 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5490 : ∀ X0 X1 : G, (M.op (M.op X1 X0) x) = (M.op (M.op X1 y) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5497 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op (M.op X1 (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq176 eq178
    | exact resolve eq178 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5505 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (σ x) (σ y))) = (M.op (M.op X1 (σ x)) (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq320 eq178
    | exact resolve eq178 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5584 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op X3 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq626 X2 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq178 X2 X0 X1 X2
       grind)
    | exact superpose eq178 eq626
    | exact resolve eq626 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5613 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 X1) (M.op X3 X4))) = (M.op (M.op (M.op (M.op X0 X1) X2) X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 (M.op X0 (M.op (M.op X2 X1) (M.op X3 X4))) X3 X4
       have i₂ := eq178 X0 X2 X1 (M.op X3 X4)
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5662 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (σ y)) (σ x)) = (M.op X0 (M.op (M.op X2 X1) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 (M.op X0 (M.op (M.op X1 X2) sF4))
       have i₂ := eq178 X0 X1 X2 sF4
       grind)
    | exact superpose eq178 eq176
    | exact resolve eq176 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5753 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X3 X2)) = (M.op (M.op X1 X3) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5489 X0 X1 X2 X3 x
       have i₂ := eq617 X2 (M.op X1 X0) X3 x
       grind)
    | exact superpose eq617 eq5489
    | exact resolve eq5489 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5489
  have eq6101 : (M.op x y) ≠ (M.op x y) ∨ (k x (M.op x y)) = (M.op x (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3963 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq3963
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3963
       grind)
    | exact resolve eq13 eq3963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6103 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3963 eq28
    | exact resolve eq28 eq3963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3963
  have eq6114 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq6103
  have eq6115 : (k x (M.op x y)) = (M.op x (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq6101
  have eq6121 : (M.op x y) = (k x (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3954 eq6115
    | exact resolve eq6115 eq3954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6115
  have eq6141 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq6114 eq40
    | exact resolve eq40 eq6114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6114
  have eq6143 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20 eq6141
    | exact resolve eq6141 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6141
  have eq6145 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq3966 eq6143
    | exact resolve eq6143 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6143
  have eq6151 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6121 eq36
    | exact resolve eq36 eq6121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq6121
  have eq6161 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq6151
    | exact resolve eq6151 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6151
  have eq6163 : (σ y) = (k (σ x) (σ y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3966 eq6161
    | exact resolve eq6161 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6161
  have eq6201 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6163 eq809
    | exact resolve eq809 eq6163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6209 : x = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6201
  have eq6225 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6209 eq42
    | exact resolve eq42 eq6209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq6209
  have eq6228 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6225
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6225
    | exact resolve eq6225 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6225
  have eq6230 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3966 eq6228
    | exact resolve eq6228 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6228
  have eq6237 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6230 eq809
    | exact resolve eq809 eq6230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6230
  have eq6244 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6237
  have eq6256 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6244 eq27
    | exact resolve eq27 eq6244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6244
  have eq6269 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6256
       have r₂ := eq3966
       grind)
    | exact resolve eq6256 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6256
  have eq6272 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6269 eq27
    | exact resolve eq27 eq6269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6273 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6269 eq176
    | exact resolve eq176 eq6269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6274 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6269 eq181
    | (have r₁ := eq181
       have r₂ := eq6269
       grind)
    | exact resolve eq181 eq6269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq6279 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6269 eq341
    | exact resolve eq341 eq6269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6282 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq6274
  have eq6285 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3966 eq6272
    | exact resolve eq6272 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3966 eq6272
  have eq6288 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq6285
  have eq6297 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op (σ x) (M.op (σ x) X0)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6279 eq177
    | exact resolve eq177 eq6279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6326 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6297 x
       have i₂ := eq617 sF2 sF2 sF2 x
       grind)
    | exact superpose eq617 eq6297
    | exact resolve eq6297 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6297
  have eq6345 : (σ y) = (M.op (M.op (k (σ y) (σ x)) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6282 eq202
    | exact resolve eq202 eq6282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6371 : (σ y) = (M.op (M.op (k (σ y) (σ x)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6269 eq6345
    | exact resolve eq6345 eq6269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6345
  have eq6385 : (σ x) ≠ (σ x) ∨ (M.op (M.op (σ x) (σ x)) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6326 eq13
    | (have j0 := eq13 (M.op (σ x) (σ x)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ x)) (σ x)
       have r₂ := eq6326
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6326
       grind)
    | exact resolve eq13 eq6326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6326
  have eq6397 : (M.op (M.op (σ x) (σ x)) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq6385
  have eq6401 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6279 eq6397
    | exact resolve eq6397 eq6279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6279 eq6397
  have eq6411 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6401 eq142
    | exact resolve eq142 eq6401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq6401
  have eq6416 : x = (k (τ (M.op (σ x) (σ x))) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq6411
    | exact resolve eq6411 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6411
  have eq6427 : x ≠ x ∨ x = (M.op (τ (M.op (σ x) (σ x))) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6416 eq857
    | (have j0 := eq857 (τ (M.op (σ x) (σ x))) x
       grind)
    | (have r₁ := eq857 (τ (M.op (σ x) (σ x))) x
       have r₂ := eq6416
       grind)
    | exact resolve eq857 eq6416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6428 : x = (M.op (τ (M.op (σ x) (σ x))) x) ∨ x = (M.op x y) := by grind
  clear eq6427
  have eq6439 : (τ (M.op (σ x) (σ x))) = (M.op (M.op x (M.op x y)) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6428 eq3960
    | exact resolve eq3960 eq6428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3960 eq6428
  have eq6455 : (τ (M.op (σ x) (σ x))) = (M.op (M.op x (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq6439
  have eq6466 : (τ (M.op (σ x) (σ x))) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3954 eq6455
    | exact resolve eq6455 eq3954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6455
  have eq6482 : x = (k (M.op (M.op x y) (M.op x y)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6466 eq6416
    | exact resolve eq6416 eq6466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6416 eq6466
  have eq6491 : x = (k (M.op (M.op x y) (M.op x y)) x) ∨ x = (M.op x y) := by grind
  clear eq6482
  have eq6499 : x ≠ x ∨ x = (M.op x (M.op (M.op x y) (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6491 eq905
    | (have j0 := eq905 (M.op (M.op x y) (M.op x y)) x
       grind)
    | (have r₁ := eq905 (M.op (M.op x y) (M.op x y)) x
       have r₂ := eq6491
       grind)
    | exact resolve eq905 eq6491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6491
  have eq6502 : x = (M.op x (M.op (M.op x y) (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq6499
  have eq6548 : (σ y) = (M.op (M.op (k (σ y) (σ x)) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6282 eq6273
    | exact resolve eq6273 eq6282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6273
  have eq6590 : (σ y) = (M.op (M.op (k (σ y) (σ x)) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq6548
  have eq7146 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq6145 eq810
    | (have j0 := eq810 (σ y) (σ x)
       grind)
    | (have r₁ := eq810 (σ y) (σ x)
       have r₂ := eq6145
       grind)
    | (have r₁ := eq810 x (M.op x y)
       have r₂ := eq6145
       grind)
    | exact resolve eq810 eq6145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7147 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq7146
  have eq7155 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq26 eq7147
    | exact resolve eq7147 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7147
  have eq7174 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq6269 eq7155
    | exact resolve eq7155 eq6269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6269 eq7155
  have eq7185 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq6163 eq7174
    | exact resolve eq7174 eq6163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6163 eq7174
  have eq7193 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | (have r₁ := eq7185
       have r₂ := eq6288
       grind)
    | exact resolve eq7185 eq6288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7185
  have eq7548 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq6145 eq6371
    | exact resolve eq6371 eq6145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6371
  have eq7588 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq7548
  have eq7599 : (σ y) = (M.op (k (σ y) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq6282 eq7588
    | exact resolve eq7588 eq6282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6282 eq7588
  have eq7605 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq6145 eq7599
    | exact resolve eq7599 eq6145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7599
  have eq7607 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq6145 eq6590
    | exact resolve eq6590 eq6145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6145 eq6590
  have eq7649 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq7607
  have eq7663 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq7605 eq7649
    | exact resolve eq7649 eq7605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7605 eq7649
  have eq7670 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq7193 eq7663
    | exact resolve eq7663 eq7193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7193 eq7663
  have eq7675 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7670
       have r₂ := eq6288
       grind)
    | exact resolve eq7670 eq6288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6288 eq7670
  have eq14804 : x = (M.op (M.op x (M.op x y)) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6502 eq16
    | exact resolve eq16 eq6502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6502
  have eq14839 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3954 eq14804
    | exact resolve eq14804 eq3954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14804
  have eq14840 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq14839
  have eq14865 : (M.op x y) = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14840 eq3958
    | exact resolve eq3958 eq14840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3958
  have eq14867 : (M.op x y) = (k (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14840 eq4626
    | (have j0 := eq4626 (M.op x y)
       grind)
    | exact resolve eq4626 eq14840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4626 eq14840
  have eq14891 : (M.op x y) = (k (M.op x (M.op x y)) x) ∨ x = (M.op x y) := by grind
  clear eq14867
  have eq14893 : (M.op x y) = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) := by grind
  clear eq14865
  have eq14913 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3954 eq14891
    | exact resolve eq14891 eq3954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14891
  have eq14914 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3954 eq14893
    | exact resolve eq14893 eq3954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14893
  have eq15034 : (M.op x y) ≠ (M.op x y) ∨ (k x (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14913 eq810
    | (have j0 := eq810 (M.op x y) x
       grind)
    | (have r₁ := eq810 (M.op x y) x
       have r₂ := eq14913
       grind)
    | exact resolve eq810 eq14913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq14913
  have eq15037 : (k x (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq15034
  have eq15038 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3954 eq15037
    | exact resolve eq15037 eq3954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3954 eq15037
  have eq15041 : x = (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7675 eq15038
    | exact resolve eq15038 eq7675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7675 eq15038
  have eq15042 : x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq15041
  have eq15045 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14914 eq15042
    | exact resolve eq15042 eq14914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14914 eq15042
  have eq15046 : x = (M.op x y) := by grind
  clear eq15045
  have eq15048 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15046
       grind)
    | exact superpose eq15046 eq18
    | exact resolve eq18 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq15049 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq15046
       grind)
    | exact superpose eq15046 eq22
    | exact resolve eq22 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq15051 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq15046
       grind)
    | exact superpose eq15046 eq40
    | exact resolve eq40 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq15053 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq180
       have i₂ := eq15046
       grind)
    | exact superpose eq15046 eq180
    | (have r₁ := eq180
       have r₂ := eq15046
       grind)
    | exact resolve eq180 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq15054 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq192 X0
       have i₂ := eq15046
       grind)
    | exact superpose eq15046 eq192
    | exact resolve eq192 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq15055 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq302 X0
       have i₂ := eq15046
       grind)
    | exact superpose eq15046 eq302
    | exact resolve eq302 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq15057 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq330
       have i₂ := eq15046
       grind)
    | exact superpose eq15046 eq330
    | exact resolve eq330 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15064 : (k y (M.op x y)) = (M.op y (M.op x y)) := by grind
  clear eq15053
  have eq15068 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15049 eq20
    | exact resolve eq20 eq15049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15078 : ∀ X0 : G, (τ (k X0 (σ x))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq15049 eq384
    | exact resolve eq384 eq15049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq15049
  have eq15137 : y ≠ (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq15048 eq12
    | (have j0 := eq12 (M.op x y) y
       grind)
    | exact resolve eq12 eq15048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15162 : y = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have r₁ := eq15137
       have r₂ := eq3951
       grind)
    | exact resolve eq15137 eq3951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15137
  have eq15170 : y = (k y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq15064 eq15162
    | exact resolve eq15162 eq15064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15162
  have eq15173 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq3951 eq15170
    | exact resolve eq15170 eq3951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15170
  have eq15215 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | exact superpose eq15048 eq183
    | exact resolve eq183 eq15048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq15546 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq15215 X0
       have i₂ := eq15046
       grind)
    | exact superpose eq15046 eq15215
    | exact resolve eq15215 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15215
  have eq15901 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq15057 eq175
    | exact resolve eq175 eq15057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq15057
  have eq15934 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq15901
       have i₂ := eq15046
       grind)
    | exact superpose eq15046 eq15901
    | exact resolve eq15901 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15901
  have eq15941 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq15546 eq15934
    | exact resolve eq15934 eq15546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15934
  have eq15963 : y ≠ (k y (M.op x y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq15064 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | exact resolve eq13 eq15064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15064
  have eq15990 : (M.op x y) = (k (M.op x y) y) ∨ y ≠ (k y (M.op x y)) := by
    first
    | exact superpose eq15048 eq15963
    | exact resolve eq15963 eq15048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15963
  have eq16000 : (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) ≠ (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3951 eq15990
    | exact resolve eq15990 eq3951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3951 eq15990
  have eq16007 : (M.op x y) = (k (M.op x y) y) := by
    first
    | (have r₁ := eq16000
       have r₂ := eq15173
       grind)
    | exact resolve eq16000 eq15173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15173 eq16000
  have eq16013 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16007 eq41
    | exact resolve eq41 eq16007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq16007
  have eq16019 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq16013
    | exact resolve eq16013 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16013
  have eq16021 : (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq15068 eq16019
    | exact resolve eq16019 eq15068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16019
  have eq16028 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16021 eq809
    | exact resolve eq809 eq16021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq16034 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq16021 eq811
    | (have j0 := eq811 (σ x) (σ y) x
       grind)
    | exact resolve eq811 eq16021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq16035 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16021 eq857
    | (have j0 := eq857 (σ x) (σ y)
       grind)
    | exact resolve eq857 eq16021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16037 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16035
    | exact resolve eq16035 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16035
  have eq16038 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16034
    | (have j0 := eq16034 X0
       grind)
    | exact resolve eq16034 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16034
  have eq16048 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq16028 eq176
    | exact resolve eq176 eq16028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17151 : (M.op (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k y (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq15941 eq13
    | (have j0 := eq13 y (M.op (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq13 y (M.op (M.op x y) (M.op x y))
       have r₂ := eq15941
       grind)
    | exact resolve eq13 eq15941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17167 : (k y (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq17151
  have eq17182 : (k y (M.op (M.op x y) (M.op x y))) = (M.op y y) := by
    first
    | exact superpose eq15055 eq17167
    | exact resolve eq17167 eq15055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15055 eq17167
  have eq17285 : (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) = (σ (M.op y y)) := by
    first
    | exact superpose eq17182 eq37
    | exact resolve eq37 eq17182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq17182
  have eq18799 : ∀ X0 X1 : G, (M.op (M.op X1 y) X0) = (M.op (M.op X1 (M.op (M.op X0 (M.op x y)) y)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq15546 eq178
    | exact resolve eq178 eq15546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15546
  have eq18852 : ∀ X0 X1 : G, (M.op (M.op X1 y) X0) = (M.op (M.op X1 (M.op x X0)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq618 eq18799
    | exact resolve eq18799 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq18799
  have eq18895 : ∀ X0 X1 : G, (M.op (M.op X1 y) X0) = (M.op (M.op X1 (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq18852 X0 X1
       have i₂ := eq15046
       grind)
    | exact superpose eq15046 eq18852
    | exact resolve eq18852 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18852
  have eq20029 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op X0 (σ y)) (σ x)) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq187 eq16038
    | exact resolve eq16038 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20140 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq5662 eq20029
    | exact resolve eq20029 eq5662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20029
  have eq20155 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq20140
    | (have j0 := eq20140 X0
       grind)
    | exact resolve eq20140 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20140
  have eq20160 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq306 eq20155
    | exact resolve eq20155 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20155
  have eq20161 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq16028 eq20160
    | exact resolve eq20160 eq16028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20160
  have eq20189 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16048
    | (have j0 := eq16048 (σ x)
       grind)
    | exact resolve eq16048 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16048
  have eq20259 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16028 eq20189
    | exact resolve eq20189 eq16028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20189
  have eq21388 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20161 eq16
    | exact resolve eq16 eq20161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22798 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21388
    | (have j0 := eq21388 (σ x)
       grind)
    | exact resolve eq21388 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22885 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16028 eq22798
    | exact resolve eq22798 eq16028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22798
  have eq22941 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op (σ x) (M.op (σ x) X0)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22885 eq177
    | exact resolve eq177 eq22885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22942 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22885 eq202
    | exact resolve eq202 eq22885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22986 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16028 eq22942
    | exact resolve eq22942 eq16028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16028 eq22942
  have eq22987 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22941 x
       have i₂ := eq617 sF2 sF2 sF2 x
       grind)
    | exact superpose eq617 eq22941
    | exact resolve eq22941 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22941
  have eq23011 : (σ x) ≠ (σ x) ∨ (M.op (M.op (σ x) (σ x)) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22987 eq13
    | (have j0 := eq13 (M.op (σ x) (σ x)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ x)) (σ x)
       have r₂ := eq22987
       grind)
    | exact resolve eq13 eq22987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22987
  have eq23028 : (M.op (M.op (σ x) (σ x)) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23011
  have eq23036 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22885 eq23028
    | exact resolve eq23028 eq22885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23028
  have eq23051 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23036 eq15078
    | exact resolve eq15078 eq23036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15078 eq23036
  have eq23060 : x = (k (τ (M.op (σ x) (σ x))) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq23051
    | exact resolve eq23051 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq23051
  have eq23062 : (M.op x y) = (k (τ (M.op (σ x) (σ x))) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23060
       have i₂ := eq15046
       grind)
    | exact superpose eq15046 eq23060
    | exact resolve eq23060 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23060
  have eq23074 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ x))) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23062 eq857
    | (have j0 := eq857 (τ (M.op (σ x) (σ x))) (M.op x y)
       grind)
    | (have r₁ := eq857 (τ (M.op (σ x) (σ x))) (M.op x y)
       have r₂ := eq23062
       grind)
    | exact resolve eq857 eq23062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23075 : (M.op x y) = (M.op (τ (M.op (σ x) (σ x))) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23074
  have eq23105 : (τ (M.op (σ x) (σ x))) = (M.op (M.op (M.op x y) (M.op x y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23075 eq15054
    | exact resolve eq15054 eq23075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15054 eq23075
  have eq23138 : (τ (M.op (σ x) (σ x))) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15941 eq23105
    | exact resolve eq23105 eq15941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15941 eq23105
  have eq23196 : (M.op (σ x) (σ x)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23138 eq14
    | exact resolve eq14 eq23138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23138
  have eq23232 : (k (σ y) (M.op (σ x) (σ x))) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23196 eq17285
    | exact resolve eq17285 eq23196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17285
  have eq23253 : (k (σ y) (M.op (σ x) (σ x))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq925 eq23232
    | exact resolve eq23232 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23232
  have eq23260 : (M.op (σ x) (σ x)) = (k (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23196 eq23253
    | exact resolve eq23253 eq23196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23196 eq23253
  have eq23889 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (M.op (σ x) (σ x))) = (k (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22986 eq13
    | (have j0 := eq13 (σ y) (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ x))
       have r₂ := eq22986
       grind)
    | exact resolve eq13 eq22986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22986
  have eq23907 : (M.op (σ y) (M.op (σ x) (σ x))) = (k (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23889
  have eq23924 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20161 eq23907
    | exact resolve eq23907 eq20161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20161 eq23907
  have eq23941 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23260 eq23924
    | exact resolve eq23924 eq23260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23260 eq23924
  have eq23991 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23941 eq21388
    | exact resolve eq21388 eq23941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21388 eq23941
  have eq24011 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23991
  have eq24027 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22885 eq24011
    | exact resolve eq24011 eq22885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22885 eq24011
  have eq24080 : (M.op x y) = (k (τ (σ y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24027 eq23062
    | exact resolve eq23062 eq24027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23062
  have eq24098 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24027 eq16038
    | exact resolve eq16038 eq24027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16038
  have eq24105 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24027 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq24027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq24027
  have eq24122 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24098
  have eq24125 : (M.op x y) = (k (τ (σ y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24080
  have eq24139 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq24105
       have r₂ := eq16037
       grind)
    | exact resolve eq24105 eq16037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24105
  have eq24141 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20259 eq24122
    | exact resolve eq24122 eq20259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20259 eq24122
  have eq24145 : (M.op x y) = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq24125
    | exact resolve eq24125 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq24125
  have eq24158 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq925 eq24145
    | exact resolve eq24145 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq24145
  have eq24464 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24158 eq15051
    | exact resolve eq15051 eq24158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24158
  have eq24477 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq24464
    | exact resolve eq24464 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24464
  have eq24481 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15068 eq24477
    | exact resolve eq24477 eq15068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24477
  have eq24513 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24481 eq24139
    | exact resolve eq24139 eq24481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24139 eq24481
  have eq24524 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24513
  have eq24532 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq24524
       have r₂ := eq16037
       grind)
    | exact resolve eq24524 eq16037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16037 eq24524
  have eq24541 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq24532 eq27
    | exact resolve eq27 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq24542 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq24532 eq176
    | exact resolve eq176 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq24544 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (σ x)) = (M.op (M.op X0 (M.op (σ y) X1)) X1) := by
    intro X0 X1
    first
    | exact superpose eq24532 eq187
    | exact resolve eq187 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24545 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq24532 eq188
    | exact resolve eq188 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq24547 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq24532 eq202
    | exact resolve eq202 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq24548 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) := by
    intro X0
    first
    | exact superpose eq24532 eq306
    | exact resolve eq306 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq24549 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq24532 eq320
    | exact resolve eq320 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24550 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
    first
    | exact superpose eq24532 eq341
    | exact resolve eq341 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq24556 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ x)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq340 eq24544
    | exact resolve eq24544 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340 eq24544
  have eq24557 : (σ x) ≠ (σ y) := by
    first
    | exact superpose eq15068 eq24541
    | exact resolve eq24541 eq15068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24541
  have eq24559 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ x)) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq24532 eq24556
    | exact resolve eq24556 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24556
  have eq24580 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op (σ x) (M.op (σ y) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq24550 eq177
    | exact resolve eq177 eq24550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq24581 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq24550 eq320
    | exact resolve eq320 eq24550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq24630 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq24532 eq24581
    | exact resolve eq24581 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24581
  have eq24631 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq24580 x
       have i₂ := eq617 sF2 sF2 sF3 x
       grind)
    | exact superpose eq617 eq24580
    | exact resolve eq24580 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq24580
  have eq24643 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24548 eq24631
    | exact resolve eq24631 eq24548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24548 eq24631
  have eq24649 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (M.op (M.op X1 (σ y)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq24532 eq621
    | exact resolve eq621 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24661 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (M.op (σ x) (M.op (M.op X0 X2) (M.op X2 (M.op (σ x) (σ y)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq621 (M.op (M.op X0 X1) (M.op X1 sF4)) X1
       have i₂ := eq632 X0 X1 sF4
       grind)
    | exact superpose eq632 eq621
    | exact resolve eq621 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24683 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) X1)) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq621 eq178
    | exact resolve eq178 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24781 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) X1)) (σ y)) = (M.op (M.op X0 (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq24532 eq24683
    | exact resolve eq24683 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24683
  have eq24801 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24661 X0 X1 x
       have i₂ := eq739 X0 sF2 x sF4
       grind)
    | exact superpose eq739 eq24661
    | exact resolve eq24661 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24661
  have eq24864 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (M.op (σ x) (M.op (σ y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq24532 eq24801
    | exact resolve eq24801 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24801
  have eq25000 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0
    first
    | exact superpose eq15048 eq5490
    | exact resolve eq5490 eq15048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5490 eq15048
  have eq25139 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq25000 X0
       have i₂ := eq15046
       grind)
    | exact superpose eq15046 eq25000
    | exact resolve eq25000 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25000
  have eq25561 : ∀ X0 : G, (M.op (M.op (M.op (M.op X0 (σ y)) (σ x)) (σ y)) (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq187 eq24542
    | exact resolve eq24542 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25615 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op (M.op X1 (σ y)) (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq24542 eq178
    | exact resolve eq178 eq24542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24542
  have eq25688 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op (M.op (M.op X0 (σ y)) (σ x)) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq24532 eq25561
    | exact resolve eq25561 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25561
  have eq25703 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq5662 eq25688
    | exact resolve eq25688 eq5662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5662 eq25688
  have eq25708 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq24532 eq25703
    | exact resolve eq25703 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25703
  have eq25710 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq24649 eq25708
    | exact resolve eq25708 eq24649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24649 eq25708
  have eq25711 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq24545 eq25710
    | exact resolve eq25710 eq24545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25710
  have eq26406 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq24630 eq24549
    | exact resolve eq24549 eq24630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24549 eq24630
  have eq26528 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq25711 eq632
    | exact resolve eq632 eq25711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq25711
  have eq27044 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq24141 eq26528
    | exact resolve eq26528 eq24141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24141
  have eq27082 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have r₁ := eq27044
       have r₂ := eq24557
       grind)
    | exact resolve eq27044 eq24557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27044
  have eq27467 : (M.op (M.op (M.op x y) (σ y)) (σ x)) = (M.op (M.op x y) (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq25139 eq187
    | exact resolve eq187 eq25139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq25139
  have eq27542 : (M.op (M.op (M.op x y) (σ y)) (σ x)) = (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq27467
       have i₂ := eq5584 sF4 sF0 sF0 sF0
       grind)
    | (have i₁ := eq27467
       have i₂ := eq5584 sF0 sF0 sF4 sF0
       grind)
    | exact superpose eq5584 eq27467
    | exact resolve eq27467 eq5584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27467
  have eq27614 : (M.op (M.op (M.op x y) (σ y)) (σ x)) = (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (σ y))) := by
    first
    | exact superpose eq24532 eq27542
    | exact resolve eq27542 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27542
  have eq27671 : (M.op (M.op (M.op x y) (σ x)) (σ y)) = (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (σ y))) := by
    first
    | exact superpose eq24559 eq27614
    | exact resolve eq27614 eq24559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27614
  have eq28997 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ y) (σ x)) (σ x)) X0) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26406 eq5497
    | exact resolve eq5497 eq26406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26406
  have eq29018 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq5497
    | (have j0 := eq5497 X0 (σ x)
       grind)
    | exact resolve eq5497 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29131 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq24532 eq29018
    | exact resolve eq29018 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29018
  have eq29144 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op X0 (σ y))) = (M.op (M.op (M.op (M.op (σ y) (σ x)) (σ x)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq24532 eq28997
    | exact resolve eq28997 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28997
  have eq29206 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op X0 (σ y))) = (M.op (σ y) (M.op (M.op (σ x) (σ x)) (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq29144 x
       have i₂ := eq5613 sF3 sF2 sF2 sF2 x
       grind)
    | exact superpose eq5613 eq29144
    | exact resolve eq29144 eq5613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29144
  have eq29255 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ x)) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq29206 x
       have i₂ := eq739 sF2 sF3 sF2 x
       grind)
    | exact superpose eq739 eq29206
    | exact resolve eq29206 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29206
  have eq29289 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ x))) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq5505 eq29255
    | exact resolve eq29255 eq5505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29255
  have eq29306 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ x))) = (M.op (M.op (σ x) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq24532 eq29289
    | exact resolve eq29289 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29289
  have eq32512 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (M.op (σ x) X0))) (σ y)) = (M.op (M.op X1 (σ y)) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq621 eq24781
    | exact resolve eq24781 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq32705 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (M.op (σ x) X0))) (σ y)) = (M.op (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq25615 eq32512
    | exact resolve eq32512 eq25615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32512
  have eq32754 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (σ y))) (σ x)) = (M.op (M.op X1 (M.op (σ x) (M.op (σ x) X0))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq24532 eq32705
    | exact resolve eq32705 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32705
  have eq32776 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (σ y))) (σ x)) = (M.op (M.op X1 (σ y)) (M.op (σ x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq24781 eq32754
    | exact resolve eq32754 eq24781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32754
  have eq32790 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (σ y))) (σ x)) = (M.op (M.op X1 (σ x)) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32776 x X1
       have i₂ := eq5753 sF3 X1 x sF2
       grind)
    | (have i₁ := eq32776 x X1
       have i₂ := eq5753 sF2 X1 x sF3
       grind)
    | exact superpose eq5753 eq32776
    | exact resolve eq32776 eq5753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32776
  have eq32944 : ∀ X0 : G, (M.op (M.op (σ x) (M.op X0 (σ y))) (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y))) := by
    intro X0
    first
    | exact superpose eq24864 eq29131
    | exact resolve eq29131 eq24864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24864 eq29131
  have eq32951 : ∀ X0 : G, (M.op (M.op (σ x) (M.op X0 (σ y))) (σ x)) = (M.op (σ y) (M.op (σ y) (M.op (M.op (σ y) X0) (σ x)))) := by
    intro X0
    first
    | exact superpose eq29306 eq32944
    | exact resolve eq32944 eq29306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32944
  have eq33052 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op X0 (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq32951 x
       have i₂ := eq4228 sF3 sF3 x sF2
       grind)
    | exact superpose eq4228 eq32951
    | exact resolve eq32951 eq4228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228 eq32951
  have eq33124 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq32790 eq33052
    | exact resolve eq33052 eq32790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32790 eq33052
  have eq34220 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (σ y) (M.op (σ x) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq33124 eq179
    | exact resolve eq179 eq33124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33124
  have eq35011 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) X0) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq34220 eq24781
    | exact resolve eq24781 eq34220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24781 eq34220
  have eq35063 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ x)) = (M.op (M.op (M.op (σ x) (σ x)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq25615 eq35011
    | exact resolve eq35011 eq25615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25615 eq35011
  have eq36355 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ x)) X0) X1) (σ x)) = (M.op (M.op (M.op (σ y) X0) (σ x)) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq35063 eq5497
    | exact resolve eq5497 eq35063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5497 eq35063
  have eq36416 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ x)) X0) X1) (σ x)) = (M.op (M.op (M.op (σ y) X0) (σ x)) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq24532 eq36355
    | exact resolve eq36355 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36355
  have eq36529 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ x)) X0) X1) (σ x)) = (M.op (M.op (M.op (σ y) X0) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq5505 eq36416
    | exact resolve eq36416 eq5505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5505 eq36416
  have eq36609 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ x)) X0) X1) (σ x)) = (M.op (M.op (M.op (σ y) X0) X1) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq24532 eq36529
    | exact resolve eq36529 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36529
  have eq36661 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) X1) (σ y)) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq36609 x x
       have i₂ := eq5613 sF2 sF2 x sF2 x
       grind)
    | exact superpose eq5613 eq36609
    | exact resolve eq36609 eq5613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5613 eq36609
  have eq36684 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) X1) (σ y)) = (M.op (σ x) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36661 X0 x
       have i₂ := eq739 X0 sF2 sF2 x
       grind)
    | exact superpose eq739 eq36661
    | exact resolve eq36661 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq36661
  have eq38996 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (σ x) (M.op (M.op X0 (σ y)) X1)) X0) := by
    intro X0 X1
    first
    | exact superpose eq36684 eq16
    | exact resolve eq16 eq36684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36684
  have eq39517 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ y) (M.op X0 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq38996 X0 (M.op x (M.op X0 sF3))
       have i₂ := eq179 sF2 (M.op X0 sF3) x
       grind)
    | exact superpose eq179 eq38996
    | exact resolve eq38996 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq38996
  have eq40782 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (M.op (σ x) X0) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39517 x (M.op sF3 X1)
       have i₂ := eq626 sF3 X1 x
       grind)
    | exact superpose eq626 eq39517
    | exact resolve eq39517 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq39517
  have eq42613 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (σ y) X1)) (M.op (σ x) X0)) = (M.op (M.op X2 (M.op (M.op (σ y) (M.op X0 X1)) X3)) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq40782 eq178
    | exact resolve eq178 eq40782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40782
  have eq42640 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (σ y)) = (M.op (M.op X2 (M.op (σ y) X1)) (M.op (σ x) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42613 X0 X1 X0 x
       have i₂ := eq178 X0 sF3 (M.op X0 X1) x
       grind)
    | exact superpose eq178 eq42613
    | exact resolve eq42613 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42613
  have eq42765 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (σ y)) = (M.op (M.op X2 (σ x)) (M.op (M.op (σ y) X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42640 X2 X1 X1
       have i₂ := eq5753 (M.op sF3 X1) X1 X2 sF2
       grind)
    | (have i₁ := eq42640 X2 X1 X1
       have i₂ := eq5753 sF2 X1 X2 (M.op sF3 X1)
       grind)
    | exact superpose eq5753 eq42640
    | exact resolve eq42640 eq5753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5753 eq42640
  have eq62457 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op x y)) (M.op X0 (M.op (M.op x y) X1))) = (M.op (M.op X2 (M.op (M.op (M.op X0 y) X1) X3)) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq18895 eq178
    | exact resolve eq178 eq18895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18895
  have eq62488 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op x y)) (M.op X0 (M.op (M.op x y) X1))) = (M.op (M.op X2 X1) (M.op X0 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62457 X0 X1 X2 x
       have i₂ := eq178 X2 (M.op X0 y) X1 x
       grind)
    | exact superpose eq178 eq62457
    | exact resolve eq62457 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq62457
  have eq64974 : (M.op x y) ≠ (M.op (M.op (M.op (M.op x y) (σ x)) (σ y)) (σ y)) ∨ (k (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op (M.op x y) (σ x)) (σ y)) (σ y))) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op (M.op x y) (σ x)) (σ y)) (σ y))) := by
    first
    | exact superpose eq27671 eq182
    | exact resolve eq182 eq27671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq27671
  have eq65032 : (k (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op (M.op x y) (σ x)) (σ y)) (σ y))) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op (M.op x y) (σ x)) (σ y)) (σ y))) := by
    first
    | (have r₁ := eq64974
       have r₂ := eq24547 (M.op x y)
       grind)
    | exact resolve eq64974 eq24547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64974
  have eq65073 : (k (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op (M.op x y) (σ x)) (σ y)) (σ y))) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op (σ y) (σ y)) (M.op (M.op x y) (σ x)))) := by
    first
    | (have i₁ := eq65032
       have i₂ := eq5584 (M.op sF0 sF2) sF3 sF3 (M.op sF0 sF0)
       grind)
    | (have i₁ := eq65032
       have i₂ := eq5584 sF3 sF3 (M.op sF0 sF2) (M.op sF0 sF0)
       grind)
    | exact superpose eq5584 eq65032
    | exact resolve eq65032 eq5584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5584 eq65032
  have eq65105 : (k (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op (M.op x y) (σ x)) (σ y)) (σ y))) = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (σ y) (σ y)) y)) := by
    first
    | exact superpose eq62488 eq65073
    | exact resolve eq65073 eq62488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62488 eq65073
  have eq65130 : (M.op (M.op (M.op x y) (M.op y (σ y))) (σ y)) = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op (M.op x y) (σ x)) (σ y)) (σ y))) := by
    first
    | exact superpose eq42765 eq65105
    | exact resolve eq65105 eq42765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42765 eq65105
  have eq65151 : (k (M.op (M.op x y) (M.op x y)) (M.op x y)) = (M.op (M.op (M.op x y) (M.op y (σ y))) (σ y)) := by
    first
    | exact superpose eq24547 eq65130
    | exact resolve eq65130 eq24547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24547 eq65130
  have eq65168 : (M.op (M.op (M.op x y) x) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq65151
       have i₂ := eq329 sF0 sF3
       grind)
    | exact superpose eq329 eq65151
    | exact resolve eq65151 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq65151
  have eq65182 : x = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq330 eq65168
    | exact resolve eq65168 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq65168
  have eq65194 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq65182
       have i₂ := eq15046
       grind)
    | exact superpose eq15046 eq65182
    | exact resolve eq65182 eq15046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15046 eq65182
  have eq65240 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
    first
    | exact superpose eq65194 eq15051
    | exact resolve eq15051 eq65194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15051 eq65194
  have eq65250 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
    first
    | exact superpose eq20 eq65240
    | exact resolve eq65240 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq65240
  have eq65252 : (σ x) = (k (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
    first
    | exact superpose eq15068 eq65250
    | exact resolve eq65250 eq15068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15068 eq65250
  have eq65269 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
    first
    | exact superpose eq65252 eq857
    | (have j0 := eq857 (σ (M.op (M.op x y) (M.op x y))) (σ x)
       grind)
    | (have r₁ := eq857 (σ (M.op (M.op x y) (M.op x y))) (σ x)
       have r₂ := eq65252
       grind)
    | exact resolve eq857 eq65252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq65270 : (σ x) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by grind
  clear eq65269
  have eq65534 : (M.op (M.op (σ x) (σ x)) (σ x)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq65270 eq26528
    | exact resolve eq26528 eq65270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26528 eq65270
  have eq65575 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq27082 eq65534
    | exact resolve eq65534 eq27082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27082 eq65534
  have eq65649 : (σ x) = (k (M.op (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq65575 eq65252
    | exact resolve eq65252 eq65575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65252 eq65575
  have eq65727 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq65649 eq905
    | (have j0 := eq905 (M.op (σ y) (σ y)) (σ x)
       grind)
    | (have r₁ := eq905 (M.op (σ y) (σ y)) (σ x)
       have r₂ := eq65649
       grind)
    | exact resolve eq905 eq65649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq65649
  have eq65730 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq65727
  have eq65732 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24545 eq65730
    | exact resolve eq65730 eq24545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24545 eq65730
  have eq66183 : (M.op (M.op (σ y) (σ x)) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq65732 eq24559
    | exact resolve eq24559 eq65732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24559 eq65732
  have eq66232 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24550 eq66183
    | exact resolve eq66183 eq24550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24550 eq66183
  have eq66233 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq66232
  have eq66310 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq66233 eq29306
    | exact resolve eq29306 eq66233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29306 eq66233
  have eq66386 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq66310
    | exact resolve eq66310 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq66310
  have eq66419 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq24532 eq66386
    | exact resolve eq66386 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24532 eq66386
  have eq66711 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq66419 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq66419
       grind)
    | exact resolve eq13 eq66419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66419
  have eq66735 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq66711
  have eq66752 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16021 eq66735
    | exact resolve eq66735 eq16021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16021 eq66735
  have eq67105 : (σ x) = (σ y) := by
    first
    | exact superpose eq66752 eq24643
    | exact resolve eq24643 eq66752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24643 eq66752
  have eq67215 : False := by grind
  exact eq67215

/-- `Equation2919`: `x = ((y ◇ (x ◇ z)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation2919 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2919 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2919.models_iff G M).mp hM
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
  have eq153 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
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
  have eq154 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq628 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq154 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq3968 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq153 X0 X1
       grind)
    | exact superpose eq153 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq153 X0 X1
       grind)
    | (have r₁ := eq13 X1 (τ X0)
       have r₂ := eq153 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X0)
       have r₂ := eq153 X0 (M.op (τ X0) X0)
       grind)
    | exact resolve eq13 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq3983 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3968 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3968
  have eq3984 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3983 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3983
  have eq4062 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3984 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3984
    | exact resolve eq3984 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3984
  have eq4121 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4062 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4062
    | (have j0 := eq4062 X0 X1
       grind)
    | exact resolve eq4062 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4062
  have eq4167 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq4121 X0 X1
       grind)
    | exact superpose eq4121 eq10
    | (have j1 := eq4121 X0 X1
       grind)
    | exact resolve eq10 eq4121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4217 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4167 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq4167
    | (have j0 := eq4167 X0 X1
       grind)
    | exact resolve eq4167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4167
  have eq4274 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq4217 X0 (σ X1)
       grind)
    | exact superpose eq4217 eq37
    | (have j1 := eq4217 X0 (σ X1)
       grind)
    | exact resolve eq37 eq4217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4217
  have eq4554 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq4274 (σ X0) X1
       grind)
    | exact superpose eq4274 eq28
    | (have j1 := eq4274 (σ X0) X1
       grind)
    | exact resolve eq28 eq4274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4274
  have eq4616 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4554 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4554
    | (have j0 := eq4554 X0 X1
       grind)
    | exact resolve eq4554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4554
  have eq4651 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4616 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4616
    | (have j0 := eq4616 X0 X1
       grind)
    | exact resolve eq4616 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4616
  have eq4661 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4651 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4651
    | (have j0 := eq4651 X0 X1
       grind)
    | exact resolve eq4651 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4651
  have eq4827 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4661 (τ X0) (τ X1)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq4661
    | (have j0 := eq4661 (τ X0) (τ X1)
       grind)
    | exact resolve eq4661 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq4661
  have eq5026 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4827 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4827
    | (have j0 := eq4827 X0 X1
       grind)
    | exact resolve eq4827 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4827
  have eq5102 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5026 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5026
    | (have j0 := eq5026 X0 X1
       grind)
    | exact resolve eq5026 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5026
  have eq5162 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5102 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5102
    | (have j0 := eq5102 X0 X1
       grind)
    | exact resolve eq5102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5102
  have eq5220 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5162 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5162
    | (have j0 := eq5162 X0 X1
       grind)
    | exact resolve eq5162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5162
  have eq5309 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq5220 X1 X0
       grind)
    | exact superpose eq5220 eq11
    | (have j1 := eq5220 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq5220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5220
  have eq5433 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5309 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq5309
    | (have j0 := eq5309 X0 X1
       grind)
    | exact resolve eq5309 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5309
  have eq5505 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5433 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5433
    | (have j0 := eq5433 (τ (σ (k X0 X1))) (τ (σ X1))
       grind)
    | exact resolve eq5433 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5433
  have eq5677 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5505 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5505
    | (have j0 := eq5505 X0 X1
       grind)
    | exact resolve eq5505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5505
  have eq5682 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5677 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5677
    | (have j0 := eq5677 X0 X1
       grind)
    | exact resolve eq5677 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5677
  have eq6208 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5682 y x
       grind)
    | exact superpose eq5682 eq16
    | (have j1 := eq5682 x y
       grind)
    | exact resolve eq16 eq5682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5682
  have eq6245 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6208
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq6208
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq6208
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6208
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6208 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6246 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq6208
       have i₂ := eq4121 x y
       grind)
    | exact superpose eq4121 eq6208
    | (have j1 := eq4121 x y
       grind)
    | (have r₁ := eq6208
       have r₂ := eq4121 x y
       grind)
    | (have r₁ := eq6208
       have r₂ := eq4121 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6208
       have r₂ := eq4121 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6208 eq4121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4121 eq6208
  have eq6249 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by grind
  clear eq6246
  have eq6250 : x = y ∨ x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq6249
  have eq6251 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq6245
  have eq6252 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6251
  have eq6255 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6250
       grind)
    | exact superpose eq6250 eq16
    | exact resolve eq16 eq6250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6250
  have eq6256 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6255
       have r₂ := eq22 x
       grind)
    | exact resolve eq6255 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6255
  have eq6260 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq628 x y
       have i₂ := eq6256
       grind)
    | exact superpose eq6256 eq628
    | (have j0 := eq628 x y
       grind)
    | exact resolve eq628 eq6256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq6256
  have eq6267 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6260
  have eq6268 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6267
  have eq6272 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6252
       grind)
    | exact superpose eq6252 eq16
    | exact resolve eq16 eq6252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6252
  have eq6273 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6272
       have r₂ := eq22 x
       grind)
    | exact resolve eq6272 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6272
  have eq6328 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6268
       grind)
    | exact superpose eq6268 eq16
    | exact resolve eq16 eq6268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6268
  have eq6356 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6328
       have i₂ := eq6273
       grind)
    | exact superpose eq6273 eq6328
    | exact resolve eq6328 eq6273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6273 eq6328
  have eq6357 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq6356
  have eq6358 : (σ x) = (σ y) := by grind
  clear eq6357
  have eq6359 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6358
       grind)
    | exact superpose eq6358 eq16
    | exact resolve eq16 eq6358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6360 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6358
       grind)
    | exact superpose eq6358 eq10
    | exact resolve eq10 eq6358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6358
  have eq6415 : x = y := by
    first
    | (have i₁ := eq6360
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6360
    | exact resolve eq6360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6360
  have eq6416 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6359
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq6359
    | exact resolve eq6359 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6359
  have eq6417 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6416
       have i₂ := eq6415
       grind)
    | exact superpose eq6415 eq6416
    | exact resolve eq6416 eq6415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6415 eq6416
  have eq6418 : False := by grind
  exact eq6418
